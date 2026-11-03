import PyLean.BytesObj.Bytes.ByteArray
import PyLean.BytesObj.Bytes.Basic

/-!
`bytearray` as a mutable heap object that Python callbacks can change while a C function of
Objects/bytearrayobject.c (CPython 3.15.2) runs.

* `H` is the heap the callbacks see: the object (`BA`, with its layout and `ob_exports`), the
  generation of its storage (`gen`, bumped whenever `ob_bytes_object` is replaced or reallocated,
  so a pointer taken before is no longer valid) and the number of views Python code holds.
* A callback is a list of statements on `self` (`Act`), each in `try: ... except Exception: pass`,
  then its result. The statements stand for the kinds of change Python code can make: an in-place
  write (`self[i] = v`), a resize through `bytearray_resize_lock_held` (`self.resize(n)`, which
  covers `clear`, `append`, `+=` and every other method that resizes), a deletion at the front
  (`del self[:k]`, which moves `ob_start` instead), and taking or releasing a `memoryview(self)`.
  Each runs through the model of that method, so it refuses exactly where CPython refuses. Scope
  limit: callbacks act on `self` only.
* `E α := H → Py α × H` threads the heap through exceptions, because a change made before an
  exception stays.
* A C pointer into the storage is `Ptr`: the generation and `ob_start - ob_bytes` when it was
  taken. `H.read` reads through it: freed storage (`uafRead`) and bytes outside the current
  contents (`staleRead`) are reported as C undefined behaviour, which is not a Python outcome.
* Argument objects (`Arg`) are C objects (`Obj`, no Python code runs), the classes `RIdx`
  (`__index__`), `RBuf` (`__buffer__`, `__release_buffer__`), `RLen` (a `bytes` subclass with
  `__len__`), `RIt` (an iterator class) and `self`.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch
open PyLean.RangeSlice (Slice sliceUnpack adjustIndices)

/-! ## The heap -/

structure H where
  ba : BA
  gen : Nat := 0
  kept : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- Whether going from `a` to `b` replaced or reallocated the storage. `bytearray_resize_storage`
(:228-260) leaves `ob_start == ob_bytes` and a new `ob_alloc` (or, for a moderate upsize from an
offset, the same `ob_alloc` and offset 0); a resize to 0 (:295-299) installs the empty bytes; the
quick exit (:309-315) and `ob_start` moves (:619, :1665) keep the storage. -/
def BA.moved (a b : BA) : Bool :=
  a.alloc != b.alloc || (a.size != 0 && b.size == 0) || (a.offset != 0 && b.offset == 0)

/-- The heap with `self` replaced by `b`. -/
def H.put (h : H) (b : BA) : H :=
  { h with ba := b, gen := if h.ba.moved b then h.gen + 1 else h.gen }

/-- One statement of a callback on `self`, run in `try: ... except Exception: pass`. -/
inductive Act where
  /-- `self[i] = v` -/
  | set (i : Int) (v : Int)
  /-- `self.resize(n)` -/
  | resize (n : Int)
  /-- `del self[:k]` -/
  | delFront (k : Int)
  /-- `views.append(memoryview(self))` -/
  | grab
  /-- `views.pop().release()` when a view is held -/
  | drop
  deriving Repr, DecidableEq, Inhabited

def Act.run (h : H) : Act → H
  | .set i v =>
    match baAssIndex h.ba i (some (.int v)) with
    | .ok b => h.put b
    | .error _ => h
  | .resize n =>
    match baResizeMethod h.ba n with
    | .ok b => h.put b
    | .error _ => h.put (baResizeLeft h.ba n)
  | .delFront k =>
    match baAssSlice h.ba ⟨none, some k, none⟩ none with
    | .ok b => h.put b
    | .error _ => h
  | .grab => { h with ba := baGetBuffer h.ba, kept := h.kept + 1 }
  | .drop => if h.kept = 0 then h else { h with ba := baReleaseBuffer h.ba, kept := h.kept - 1 }

def runActs (h : H) (acts : List Act) : H := acts.foldl Act.run h

/-! ## The effect monad -/

def E (α : Type) : Type := H → Py α × H

namespace E

protected def pure {α : Type} (a : α) : E α := fun h => (.ok a, h)

protected def bind {α β : Type} (x : E α) (f : α → E β) : E β := fun h =>
  match x h with
  | (.ok a, h') => f a h'
  | (.error e, h') => (.error e, h')

instance : Monad E where
  pure := E.pure
  bind := E.bind

instance : MonadExceptOf PyExc E where
  throw e := fun h => (.error e, h)
  tryCatch x handler := fun h =>
    match x h with
    | (.ok a, h') => (.ok a, h')
    | (.error e, h') => handler e h'

def get : E H := fun h => (.ok h, h)

def modify (f : H → H) : E Unit := fun h => (.ok (), f h)

def lift {α : Type} (p : Py α) : E α := fun h => (p, h)

/-- Run `x` and keep its exception as a value. -/
def attempt {α : Type} (x : E α) : E (Py α) := fun h =>
  let (r, h') := x h
  (.ok r, h')

@[simp] theorem pure_app {α : Type} (a : α) (h : H) : (pure a : E α) h = (.ok a, h) := rfl

@[simp] theorem bind_app {α β : Type} (x : E α) (f : α → E β) (h : H) :
    (x >>= f) h = match x h with
      | (.ok a, h') => f a h'
      | (.error e, h') => (.error e, h') := rfl

@[simp] theorem throw_app {α : Type} (e : PyExc) (h : H) : (throw e : E α) h = (.error e, h) := rfl

@[simp] theorem get_app (h : H) : get h = (.ok h, h) := rfl

@[simp] theorem modify_app (f : H → H) (h : H) : modify f h = (.ok (), f h) := rfl

@[simp] theorem lift_app {α : Type} (p : Py α) (h : H) : lift p h = (p, h) := rfl

@[simp] theorem attempt_app {α : Type} (x : E α) (h : H) : attempt x h = (.ok (x h).1, (x h).2) := rfl

end E

/-- A callback: its statements, then its result. -/
def runCb {α : Type} (acts : List Act) (res : Py α) : E α := fun h => (res, runActs h acts)

/-- The current contents. -/
def curSeq : E Seq := fun h => (.ok h.ba.seq, h)

/-- `Py_SIZE(self)`. -/
def curSize : E Int := fun h => (.ok h.ba.size, h)

/-- Apply a method of the pure model to `self`; a failure leaves `self` as it was. -/
def liftBA (f : BA → Py BA) : E Unit := fun h =>
  match f h.ba with
  | .ok b => (.ok (), h.put b)
  | .error e => (.error e, h)

/-- The same for a method with a result. -/
def liftBAR {α : Type} (f : BA → Py (α × BA)) : E α := fun h =>
  match f h.ba with
  | .ok (a, b) => (.ok a, h.put b)
  | .error e => (.error e, h)

/-- `bytearray_resize_lock_held(self, n)`, :263-343. A failure leaves `baResizeLeft`. -/
def resizeE (n : Int) : E Unit := fun h =>
  match baResize h.ba n with
  | .ok b => (.ok (), h.put b)
  | .error e => (.error e, h.put (baResizeLeft h.ba n))

/-- `_canresize(self)`, :127-136. -/
def canResizeE : E Unit := fun h => (canResize h.ba, h)

def exportsUp : E Unit := E.modify fun h => { h with ba := baGetBuffer h.ba }

def exportsDown : E Unit := E.modify fun h => { h with ba := baReleaseBuffer h.ba }

/-! ## Pointers into the storage -/

structure Ptr where
  gen : Nat
  start : Int
  deriving Repr, DecidableEq

/-- `PyByteArray_AS_STRING(self)`. -/
def H.ptr (h : H) : Ptr := ⟨h.gen, h.ba.offset⟩

def uafRead : PyExc := .named "CUndefinedBehaviour" "~read of freed bytearray storage"

def staleRead : PyExc := .named "CUndefinedBehaviour" "~read outside the bytes of the bytearray"

/-- Read `n` bytes at `p + i` in heap `h`. Zero bytes read nothing. -/
def H.read (h : H) (p : Ptr) (i n : Int) : Py Seq :=
  if n = 0 then .ok []
  else if p.gen ≠ h.gen then .error uafRead
  else
    let j := p.start + i - h.ba.offset
    if 0 ≤ j ∧ 0 ≤ n ∧ j + n ≤ h.ba.size then
      .ok (((h.ba.data.drop j.toNat).take n.toNat).map Int.toNat)
    else .error staleRead

def readE (p : Ptr) (i n : Int) : E Seq := fun h => (h.read p i n, h)

/-! ## Argument objects -/

/-- An item a scripted iterator yields. -/
inductive Item where
  | obj (o : Obj)
  | idx (acts : List Act) (res : Py Int)
  | buf (acts : List Act) (res : Py Seq) (rel : List Act)
  | me
  deriving Inhabited

inductive Arg where
  /-- A C object: no Python code runs. -/
  | obj (o : Obj)
  /-- `class RIdx: def __index__(self): <acts>; return/raise <res>` -/
  | idx (acts : List Act) (res : Py Int)
  /-- `class RBuf`: `__buffer__` runs `acts` and returns `memoryview(bytes(res))`;
  `__release_buffer__` runs `rel`. -/
  | buf (acts : List Act) (res : Py Seq) (rel : List Act)
  /-- `class RLen(bytes)` holding `s`, whose `__len__` runs `acts` and returns `res`. -/
  | slen (acts : List Act) (res : Py Int) (s : Seq)
  /-- `class RIt`: `__next__` runs each step's statements and returns its item, then runs `finActs`
  and raises `fin` (`none`: `StopIteration`). -/
  | it (steps : List (List Act × Item)) (finActs : List Act) (fin : Option PyExc)
  /-- `self` -/
  | me
  deriving Inhabited

def Item.toArg : Item → Arg
  | .obj o => .obj o
  | .idx a r => .idx a r
  | .buf a r l => .buf a r l
  | .me => .me

def Arg.typeName : Arg → String
  | .obj o => o.typeName
  | .idx .. => "RIdx"
  | .buf .. => "RBuf"
  | .slen .. => "RLen"
  | .it .. => "RIt"
  | .me => "bytearray"

/-- `_PyIndex_Check`. -/
def Arg.indexCheck : Arg → Bool
  | .obj o => o.index?.isSome
  | .idx .. => true
  | _ => false

/-- `PyObject_CheckBuffer`. -/
def Arg.bufferCheck : Arg → Bool
  | .obj o => o.buffer?.isSome
  | .buf .. | .slen .. | .me => true
  | _ => false

/-- `PyNumber_Check`. -/
def Arg.numberCheck : Arg → Bool
  | .obj o => o.isNumber
  | .idx .. => true
  | _ => false

def Arg.isNone : Arg → Bool
  | .obj .none => true
  | _ => false

/-- `_PyNumber_Index(a)`. -/
def indexE : Arg → E Int
  | .obj o =>
    match o.index? with
    | some r => E.lift r
    | none => throw (notInteger o)
  | .idx acts res => runCb acts res
  | a => throw (.typeError s!"'{a.typeName}' object cannot be interpreted as an integer")

/-- `PyNumber_AsSsize_t(a, exc)`, Objects/abstract.c: `none` for a `NULL` exception clamps. -/
def asSsizeE (exc : Option (String → PyExc)) (a : Arg) : E Int := do
  let v ← indexE a
  match exc with
  | none => return clampSsize v
  | some mk =>
    if ssizeMin ≤ v ∧ v ≤ ssizeMax then return v
    else throw (mk s!"cannot fit '{a.typeName}' into an index-sized integer")

/-- An Argument Clinic `Py_ssize_t` parameter: `_PyNumber_Index`, then `PyLong_AsSsize_t`. -/
def clinicSsizeE (a : Arg) : E Int := do
  let v ← indexE a
  E.lift (Sequences.asSsize v)

/-- An Argument Clinic `slice_index` parameter (`_PyEval_SliceIndex`, Python/ceval.c:2949-2979):
`None` keeps the default. -/
def sliceIndexE : Option Arg → E (Option Int)
  | none => pure none
  | some a =>
    if a.isNone then pure none
    else if a.indexCheck then some <$> asSsizeE none a
    else throw (.typeError "slice indices must be integers or have an __index__ method")

/-- `_getbytevalue`, :25-44: `PyLong_AsLongAndOverflow` runs `__index__` of a non-int; an overflow
of C `long` is the same `ValueError`. -/
def getByteValueE (a : Arg) : E Nat := do
  let v ← indexE a
  if v < 0 ∨ v ≥ 256 then throw (.valueError "byte must be in range(0, 256)")
  return v.toNat

/-! ## Buffers -/

inductive View where
  | bytes (s : Seq)
  /-- A view of `self`: the pointer and the length when it was taken. -/
  | self (p : Ptr) (n : Int)

/-- A `Py_buffer` the C code holds, and what `PyBuffer_Release` runs. -/
structure Buf where
  view : View
  rel : E Unit

def Buf.len (b : Buf) : Int :=
  match b.view with
  | .bytes s => s.length
  | .self _ n => n

def Buf.read (b : Buf) : E Seq :=
  match b.view with
  | .bytes s => pure s
  | .self p n => readE p 0 n

def noRel : E Unit := pure ()

/-- `PyObject_GetBuffer(a, view, flags)`. -/
def getBufE : Arg → E Buf
  | .obj o =>
    match o.buffer? with
    | some s => pure ⟨.bytes s, noRel⟩
    | none => throw (notBytesLike o)
  | .buf acts res rel => do
    let s ← runCb acts res
    pure ⟨.bytes s, runCb rel (.ok ())⟩
  | .slen _ _ s => pure ⟨.bytes s, noRel⟩
  | .me => fun h =>
    (.ok ⟨.self h.ptr h.ba.size, exportsDown⟩, { h with ba := baGetBuffer h.ba })
  | a => throw (.typeError s!"a bytes-like object is required, not '{a.typeName}'")

/-- `PyObject_Length(a)`. -/
def lengthE : Arg → E Int
  | .obj o => E.lift ((fun (n : Nat) => (n : Int)) <$> objLength o)
  | .slen acts res _ => do
    -- `slot_sq_length`, Objects/typeobject.c: the value must be a non-negative `Py_ssize_t`
    let v ← runCb acts res
    if v < 0 then throw (.valueError "__len__() should return >= 0")
    if v > ssizeMax then throw (.overflowError "cannot fit 'int' into an index-sized integer")
    return v
  | .me => curSize
  | a => throw (.typeError s!"object of type '{a.typeName}' has no len()")

/-- The steps of `PyObject_GetIter(a)` and its `__next__`, or the error of `PyObject_GetIter`
(a `TypeError` becomes `msg`). -/
def getIterE (msg : PyExc) : Arg → E (List (List Act × Item) × List Act × Option PyExc)
  | .obj o => do
    let xs ← E.lift (getIterOr msg o)
    let fin := match iterFinish o with
      | .ok () => none
      | .error e => some e
    pure (xs.map (fun x => ([], Item.obj x)), [], fin)
  | .it steps finActs fin => pure (steps, finActs, fin)
  | _ => throw msg

/-- `PyObject_LengthHint(a, d)`: the iterator class has neither `__len__` nor `__length_hint__`. -/
def lengthHintE (a : Arg) (d : Int) : E Int :=
  match a with
  | .obj o => E.lift (lengthHint o d)
  | _ => pure d

/-! ## Search methods: `_bytearray_with_buffer`, :112-125 -/

/-- `_bytearray_with_buffer(self, op, ...)`, :112-125, and the same steps in `bytearray_contains`,
`split`, `rsplit`, `join` and `%`: `ob_exports` is raised, `op` gets `PyByteArray_AS_STRING(self)`
and `Py_SIZE(self)` as they are then, and `ob_exports` is lowered whatever `op` returned. -/
def withBufferE {α : Type} (op : Ptr → Int → E α) : E α := fun h =>
  let h1 := { h with ba := baGetBuffer h.ba }
  let (r, h2) := op h.ptr h.ba.size h1
  (r, { h2 with ba := baReleaseBuffer h2.ba })

/-- What `parse_args_finds_byte`, bytes_methods.c:403-430, leaves: a buffer object, or a byte. -/
inductive FindSub where
  | obj (a : Arg)
  | byte (v : Int)

def parseFindsByteE (sub : Arg) : E FindSub := do
  if sub.bufferCheck then return .obj sub
  if !sub.indexCheck then
    throw (.typeError s!"argument should be integer or bytes-like object, not '{sub.typeName}'")
  let ival ← asSsizeE none sub
  if ival < 0 ∨ ival > 255 then throw (.valueError "byte must be in range(0, 256)")
  return .byte ival

/-- `find_internal(str, len, ...)`, bytes_methods.c:450-507: `str` is read through `p`. `rd` is
how the search reads `str` (the C code: through the pointer). -/
def findInternalE (rd : Ptr → Int → E Seq) (p : Ptr) (len : Int) (sub : Arg) (start «end» : Int)
    (forward : Bool) : E Int := do
  match ← parseFindsByteE sub with
  | .byte v =>
    let s ← rd p len
    E.lift (bytesFindInternal s (.byte v) start «end» forward)
  | .obj a =>
    let b ← getBufE a
    let s ← rd p len
    let t ← b.read
    let r := bytesFindInternal s (.buf t) start «end» forward
    b.rel
    E.lift r

/-- `_Py_bytes_count`, bytes_methods.c:562-599. -/
def countE (rd : Ptr → Int → E Seq) (p : Ptr) (len : Int) (sub : Arg) (start «end» : Int) : E Int := do
  match ← parseFindsByteE sub with
  | .byte v =>
    let s ← rd p len
    E.lift (bytesCount s (.byte v) (some start) (some «end»))
  | .obj a =>
    let b ← getBufE a
    let s ← rd p len
    let t ← b.read
    let r := bytesCount s (.buf t) (some start) (some «end»)
    b.rel
    E.lift r

/-- The reader of the C code: through the pointer taken at the start. -/
def cRead : Ptr → Int → E Seq := fun p n => readE p 0 n

/-- The reader of the specification: the object as it is at that moment. -/
def liveRead : Ptr → Int → E Seq := fun _ _ => curSeq

/-- `bytearray.find(sub, start, end)` (`forward`) and `rfind`, :1336-1342 and :1418-1424, with the
clinic `slice_index` conversions of `start` and `end` before the body. -/
def baFindE (rd : Ptr → Int → E Seq) (sub : Arg) (start «end» : Option Arg) (forward : Bool) : E Int := do
  let st ← sliceIndexE start
  let en ← sliceIndexE «end»
  withBufferE fun p n => findInternalE rd p n sub (st.getD 0) (en.getD ssizeMax) forward

/-- `bytearray.index` and `rindex`, :1400-1406, :1436-1442 (`_Py_bytes_index`, `_Py_bytes_rindex`). -/
def baIndexE (rd : Ptr → Int → E Seq) (sub : Arg) (start «end» : Option Arg) (forward : Bool) : E Int := do
  let st ← sliceIndexE start
  let en ← sliceIndexE «end»
  withBufferE fun p n => do
    let r ← findInternalE rd p n sub (st.getD 0) (en.getD ssizeMax) forward
    if r = -1 then throw (.valueError "subsection not found")
    return r

/-- `bytearray.count`, :1352-1358. -/
def baCountE (rd : Ptr → Int → E Seq) (sub : Arg) (start «end» : Option Arg) : E Int := do
  let st ← sliceIndexE start
  let en ← sliceIndexE «end»
  withBufferE fun p n => countE rd p n sub (st.getD 0) (en.getD ssizeMax)

/-- `tailmatch`, bytes_methods.c:629-673: an exact `bytes` is read directly, anything else
through `PyObject_GetBuffer`. -/
def tailmatchE (rd : Ptr → Int → E Seq) (p : Ptr) (len : Int) (sub : Arg) (start «end» : Int)
    (forward : Bool) : E Bool := do
  let b ← getBufE sub
  let s ← rd p len
  let t ← b.read
  let r := bytesTailmatch s t start «end» forward
  b.rel
  return r

/-- The argument of `startswith`/`endswith`: one object or a tuple. -/
inductive AffixArg where
  | one (a : Arg)
  | tuple (items : List Arg)

def tailLoopE (rd : Ptr → Int → E Seq) (p : Ptr) (len : Int) (start «end» : Int) (forward : Bool) :
    List Arg → E Bool
  | [] => pure false
  | item :: rest => do
    if ← tailmatchE rd p len item start «end» forward then return true
    tailLoopE rd p len start «end» forward rest

/-- `_Py_bytes_tailmatch`, bytes_methods.c:675-706: in a tuple every error passes on; for one
object a `TypeError` (a subclass too) gets the method's message. -/
def baTailmatchE (rd : Ptr → Int → E Seq) (fname : String) (sub : AffixArg) (start «end» : Option Arg)
    (forward : Bool) : E Bool := do
  let st ← sliceIndexE start
  let en ← sliceIndexE «end»
  withBufferE fun p n =>
    match sub with
    | .tuple items => tailLoopE rd p n (st.getD 0) (en.getD ssizeMax) forward items
    | .one a => do
      match ← E.attempt (tailmatchE rd p n a (st.getD 0) (en.getD ssizeMax) forward) with
      | .ok r => return r
      | .error e =>
        if isTypeError e then
          throw (.typeError s!"{fname} first arg must be bytes or a tuple of bytes, not {a.typeName}")
        else throw e

/-- `bytearray_contains`, :1444-1459, with `_Py_bytes_contains`, bytes_methods.c:601-622: the
`PyNumber_AsSsize_t` error is cleared and the buffer protocol tried. -/
def baContainsE (rd : Ptr → Int → E Seq) (arg : Arg) : E Bool :=
  withBufferE fun p n => do
    match ← E.attempt (asSsizeE none arg) with
    | .error _ =>
      let b ← getBufE arg
      let s ← rd p n
      let t ← b.read
      let r := decide (stringlibFind s t 0 ≥ 0)
      b.rel
      return r
    | .ok ival =>
      if ival < 0 ∨ ival ≥ 256 then throw (.valueError "byte must be in range(0, 256)")
      let s ← rd p n
      return s.contains ival.toNat

/-! ## strip, :2427-2571 -/

/-- The two loops of `bytearray_strip_impl_helper`, :2448-2459: `left` and `right`. -/
def stripBounds (mem : Nat → Bool) (t : StripType) (s : Seq) : Nat × Nat :=
  let i := if t ≠ .right then (s.takeWhile mem).length else 0
  let j := if t ≠ .left then i + ((s.drop i).reverse.dropWhile mem).length else s.length
  (i, j)

theorem stripWith_bounds (mem : Nat → Bool) (t : StripType) (s : Seq) :
    stripWith mem t s = (s.drop (stripBounds mem t s).1).take ((stripBounds mem t s).2 - (stripBounds mem t s).1) := rfl

/-- `bytearray_strip_impl_helper(self, bytes, striptype)`, :2427-2463. The argument's buffer is
taken (:2440), `myptr` and `mysize` read (:2445-2446), the bounds found, the buffer released
(:2460-2461), and only then are the bytes copied from `myptr` (:2462). `copyAfter = false` is the
order that copies before the release. -/
def baStripE (copyAfter : Bool) (bytes : Option Arg) (t : StripType) : E Seq := do
  let b : Option Buf ← match bytes with
    | none => pure none
    | some a => if a.isNone then pure none else some <$> getBufE a
  let h ← E.get
  let p := h.ptr
  let mysize := h.ba.size
  let my ← readE p 0 mysize
  let cs ← match b with
    | none => pure [9, 10, 13, 12, 11, 32]
    | some b => b.read
  let (left, right) := stripBounds (fun c => cs.contains c) t my
  if copyAfter then
    match b with
    | none => pure ()
    | some b => b.rel
    readE p left (right - left)
  else
    let r ← readE p left (right - left)
    match b with
    | none => pure ()
    | some b => b.rel
    return r

/-! ## Subscripts, :508-957 -/

/-- A subscript: one object (an index or anything else), or a slice of objects. -/
inductive Key where
  | one (a : Arg)
  | slice (start stop step : Option Arg)

def Key.typeName : Key → String
  | .one a => a.typeName
  | .slice .. => "slice"

/-- `_PyEval_SliceIndex` inside `PySlice_Unpack`: `None` is absent. -/
def slicePartE : Option Arg → E (Option Int)
  | none => pure none
  | some a =>
    if a.isNone then pure none
    else if a.indexCheck then some <$> asSsizeE none a
    else throw (.typeError "slice indices must be integers or have an __index__ method")

/-- `PySlice_Unpack`, Objects/sliceobject.c:219-262: `step`, then `start`, then `stop`. -/
def sliceUnpackE (start stop step : Option Arg) : E (Int × Int × Int) := do
  let stepV ← slicePartE step
  let stepV ← match stepV with
    | none => pure 1
    | some v =>
      if v = 0 then throw (.valueError "slice step cannot be zero")
      else pure (if v < -ssizeMax then -ssizeMax else v)
  let startV ← slicePartE start
  let startV := startV.getD (if stepV < 0 then ssizeMax else 0)
  let stopV ← slicePartE stop
  let stopV := stopV.getD (if stepV < 0 then ssizeMin else ssizeMax)
  return (startV, stopV, stepV)

/-- The result of a subscript: a byte or a new bytearray. -/
inductive SubRes where
  | byte (v : Int)
  | slice (s : Seq)
  deriving Repr, DecidableEq

/-- `bytearray_subscript_lock_held`, :530-588, and `bytearray_subscript`, :590-599. The size is
read after `__index__` ran. -/
def baSubscriptE : Key → E SubRes
  | .one a => do
    if !a.indexCheck then
      throw (.typeError s!"bytearray indices must be integers or slices, not {a.typeName}")
    let i ← asSsizeE (some .indexError) a
    let size ← curSize
    let i := if i < 0 then i + size else i
    if i < 0 ∨ i ≥ size then throw (.indexError "bytearray index out of range")
    let h ← E.get
    return .byte (h.ba.data.getD i.toNat 0)
  | .slice start stop step => do
    let (start, stop, step) ← sliceUnpackE start stop step
    let size ← curSize
    let (start, _, len) := adjustIndices size start stop step
    let s ← curSeq
    if len ≤ 0 then return .slice []
    if step = 1 then return .slice ((s.drop start.toNat).take len.toNat)
    return .slice ((slicePositions start step len.toNat).map (fun q => s.getD q.toNat 0))

/-- `bytearray_setitem_lock_held`, :740-769, and `bytearray_setitem`, :771-779 (`sq_ass_item`): the
value is converted before the size is read (GH-91153). -/
def baSetItemE (i : Int) (value : Option Arg) : E Unit := do
  let ival ← match value with
    | some v => some <$> getByteValueE v
    | none => pure none
  let size ← curSize
  let i := if i < 0 then i + size else i
  if i < 0 ∨ i ≥ size then throw (.indexError "bytearray index out of range")
  match ival with
  | none => liftBA fun b => baSetslice b i (i + 1) none
  | some v => liftBA fun b => .ok { b with data := b.data.set i.toNat (v : Int) }

/-- What `__next__` gives the loops: the item, or the end (`none`). -/
def iterStepE : List (List Act × Item) → List Act → Option PyExc → Nat → E (Option (Item × Nat))
  | steps, finActs, fin, i =>
    match steps.drop i with
    | (acts, item) :: _ => do
      runCb acts (.ok ())
      return some (item, i + 1)
    | [] => do
      runCb finActs (.ok ())
      match fin with
      | none => return none
      | some e => if excMatches e "StopIteration" then return none else throw e

/-- The loop of `bytearray_extend_impl`, :2286-2321, over the steps from index `i`: each item
goes through `_getbytevalue`, a `TypeError` for a `str` argument gets its own message. -/
def extendLoopE (steps : List (List Act × Item)) (finActs : List Act) (fin : Option PyExc)
    (isStr : Bool) : Nat → List Nat → E (List Nat)
  | fuel + 1, acc => do
    match ← iterStepE steps finActs fin (acc.length) with
    | none => return acc
    | some (item, _) =>
      match ← E.attempt (getByteValueE item.toArg) with
      | .error e =>
        if isTypeError e ∧ isStr then throw (.typeError "expected iterable of integers; got: 'str'")
        else throw e
      | .ok v => extendLoopE steps finActs fin isStr fuel (acc ++ [v])
  | 0, _ => throw .modelFuel

/-- `PyByteArray_FromObject(values)` on a right-hand side that is not `self` and not a number or
a `str`: `bytearray(values)`, whose `__buffer__` or iterator can run Python code. -/
def fromObjectE (v : Arg) : E Seq :=
  match v with
  | .obj o => E.lift (BA.seq <$> baNew (some o) none none)
  | .buf acts res rel => do
    let s ← runCb acts res
    let _ ← E.lift (baFromStringAndSize none s.length)
    runCb rel (.ok ())
    return s
  | .slen _ _ s => pure s
  | .me => curSeq
  | .it steps finActs fin => do
    -- the iterator loop of `__init__` on the new object, which Python code cannot reach
    let vals ← extendLoopE steps finActs fin false (steps.length + 1) []
    return vals
  | a => throw (.typeError s!"cannot convert '{a.typeName}' object to bytearray")

/-- The slice branch of `bytearray_ass_subscript_lock_held`, :828-940, once `values` is `NULL` or a
`bytearray` (`bytes`). -/
def assSliceCore (start stop step : Option Arg) (bytes : Option Seq) : E Unit := do
  let (start, stop, step) ← sliceUnpackE start stop step
  let size ← curSize
  let (start, stop, slicelen) := adjustIndices size start stop step
  let bytes := seqData (bytes.getD [])
  -- Make sure b[5:2] = ... inserts before 5, not before 2.
  let stop := if (step < 0 ∧ start < stop) ∨ (step > 0 ∧ start > stop) then start else stop
  if step = 1 then liftBA fun b => baSetsliceLinear b start stop bytes
  else liftBA fun b => baAssExtended b start stop step slicelen bytes

/-- `bytearray_ass_subscript_lock_held`, :781-940, and `bytearray_ass_subscript`, :942-957. A value
that needs converting (`self`, or not a `bytearray`) is copied with `PyByteArray_FromObject`
and the function called again (:856-862), so the slice is unpacked twice. -/
def baAssSubE : Key → Option Arg → E Unit
  | .one a, values => do
    if !a.indexCheck then
      throw (.typeError s!"bytearray indices must be integers or slices, not {a.typeName}")
    let i ← asSsizeE (some .indexError) a
    let ival ← match values with
      | some v => some <$> getByteValueE v
      | none => pure none
    let size ← curSize
    let i := if i < 0 then i + size else i
    if i < 0 ∨ i ≥ size then throw (.indexError "bytearray index out of range")
    match ival with
    | none => liftBA fun b => baSetsliceLinear b i (i + 1) []
    | some v => liftBA fun b => .ok { b with data := b.data.set i.toNat (v : Int) }
  | .slice start stop step, none => assSliceCore start stop step none
  | .slice start stop step, some v => do
    match v with
    | .obj (.bytearray s) => assSliceCore start stop step (some s)
    | _ => do
      -- the slice is unpacked once before the value is looked at (:829-833)
      let _ ← sliceUnpackE start stop step
      let isStrV : Bool := match v with
        | .obj (.str _) => true
        | _ => false
      if v.numberCheck || isStrV then
        throw (.typeError "can assign only bytes, buffers, or iterables of ints in range(0, 256)")
      let copy ← fromObjectE v
      assSliceCore start stop step (some copy)

/-- `bytearray_setslice(self, lo, hi, values)`, :686-738: the value's `__buffer__` runs before
the clamps, which use the size after it (gh-153578); the buffer is released after the splice. -/
def baSetsliceE (lo hi : Int) (values : Option Arg) : E Unit := do
  let (bytes, rel) ← match values with
    | none => pure ([], noRel)
    | some .me => do
      let s ← curSeq
      pure (s, noRel)
    | some v => do
      match ← E.attempt (getBufE v) with
      | .error _ => throw (.typeError s!"can't set bytearray slice from {v.typeName}")
      | .ok b =>
        let s ← b.read
        pure (s, b.rel)
  let size ← curSize
  let lo := if lo < 0 then 0 else if lo > size then size else lo
  let hi := if hi < lo then lo else hi
  let hi := if hi > size then size else hi
  let r ← E.attempt (liftBA fun b => baSetsliceLinear b lo hi (seqData bytes))
  rel
  E.lift r

/-! ## Mutating methods -/

/-- `bytearray.insert(index, item)`: the clinic converts `index` (`_PyNumber_Index`,
`PyLong_AsSsize_t`) and then `item` (`_getbytevalue`), and `bytearray_insert_impl`, :2074-2096,
reads the size afterwards. -/
def baInsertE (index item : Arg) : E Unit := do
  let i ← clinicSsizeE index
  let v ← getByteValueE item
  liftBA fun b => baInsert b i (.int v)

/-- `bytearray.append(item)`, :2189-2201. -/
def baAppendE (item : Arg) : E Unit := do
  let v ← getByteValueE item
  liftBA fun b => baAppend b (.int v)

/-- `bytearray.remove(value)`, :2401-2421. -/
def baRemoveE (value : Arg) : E Unit := do
  let v ← getByteValueE value
  liftBA fun b => baRemove b (.int v)

/-- `bytearray.pop(index)`, :2359-2388. -/
def baPopE (index : Option Arg) : E Int := do
  let i ← match index with
    | none => pure (-1)
    | some a => clinicSsizeE a
  liftBAR fun b => baPop b (some i)

/-- `bytearray.take_bytes(n)`, :1614-1688: the size is read again after `__index__`. -/
def baTakeBytesE (n : Option Arg) : E Seq := do
  let toTake ← match n with
    | none => curSize
    | some a =>
      if a.isNone then curSize
      else if a.indexCheck then do
        let t ← asSsizeE (some .indexError) a
        let size ← curSize
        pure (if t < 0 then t + size else t)
      else throw (.typeError "n must be an integer or None")
  liftBAR fun b => baTakeCore b toTake

/-- `bytearray_iconcat_lock_held`, :400-427: every failure of `PyObject_GetBuffer` becomes the
`TypeError`; the size is read after the value's `__buffer__`. -/
def baIConcatE (other : Arg) : E Unit := do
  let b ← match ← E.attempt (getBufE other) with
    | .error _ => throw (.typeError s!"can't concat {other.typeName} to bytearray")
    | .ok b => pure b
  let size ← curSize
  if size > baSizeMax - b.len then
    b.rel
    throw memoryError
  match ← E.attempt (resizeE (size + b.len)) with
  | .error e =>
    b.rel
    throw e
  | .ok () =>
    let src ← b.read
    E.modify fun h => { h with ba := { h.ba with data := h.ba.data.take size.toNat ++ seqData src } }
    b.rel

/-- `PyByteArray_Concat(self, b)`, :355-390: `self + b`. -/
def baConcatE (other : Arg) : E Seq := do
  let va ← getBufE .me
  let vb ← match ← E.attempt (getBufE other) with
    | .error _ =>
      va.rel
      throw (.typeError s!"can't concat {other.typeName} to bytearray")
    | .ok b => pure b
  if va.len > baSizeMax - vb.len then
    va.rel
    vb.rel
    throw memoryError
  match baFromStringAndSize none (va.len + vb.len) with
  | .error e =>
    va.rel
    vb.rel
    throw e
  | .ok _ =>
    let a ← va.read
    let c ← vb.read
    va.rel
    vb.rel
    return a ++ c

/-- `bytearray.extend(iterable_of_ints)`, :2245-2343: a buffer goes through `bytearray_setslice` at
the size read then (:2256); otherwise the items go to a temporary, which is appended at the
size read at the end (:2335). -/
def baExtendE (x : Arg) : E Unit := do
  if x.bufferCheck then
    let size ← curSize
    baSetsliceE size size (some x)
  else
    let (steps, finActs, fin) ← getIterE (.typeError s!"can't extend bytearray with {x.typeName}") x
    let bufSize ← lengthHintE x 32
    let _ ← E.lift (baFromStringAndSize none bufSize)
    let isStr : Bool := match x with | .obj (.str _) => true | _ => false
    let vals ← extendLoopE steps finActs fin isStr (steps.length + 1) []
    let size ← curSize
    liftBA fun b => baSetsliceLinear b size size (vals.map (fun (c : Nat) => (c : Int)))

/-! ## `__init__`, :982-1182 -/

/-- The codec of `bytearray(str, encoding)`: a C codec (ascii, latin-1), or one written in Python,
which runs `acts` and returns `res`; `unique` is whether the codec keeps no other reference to the
`bytes` it returns. -/
inductive Codec where
  | builtin
  | py (acts : List Act) (res : Py Seq) (unique : Bool)

/-- The iterator loop of `bytearray___init___impl`, :1142-1172. -/
def initLoopE (steps : List (List Act × Item)) (finActs : List Act) (fin : Option PyExc) :
    Nat → Nat → E Unit
  | fuel + 1, i => do
    match ← iterStepE steps finActs fin i with
    | none => return ()
    | some (item, j) =>
      let v ← getByteValueE item.toArg
      liftBA fun b => baInitLoop b [.int (v : Int)]
      initLoopE steps finActs fin fuel j
  | 0, _ => throw .modelFuel

def encNoArg (encoding errors : Bool) : E Unit :=
  if encoding then throw (.typeError "encoding without a string argument")
  else if errors then throw (.typeError "errors without a string argument")
  else pure ()

/-- `bytearray___init___impl(self, arg, encoding, errors)`, :982-1182. -/
def baInitE (arg : Option Arg) (encoding : Option (String × Codec)) (errors : Option String) : E Unit := do
  canResizeE
  resizeE 0
  match arg with
  | none => encNoArg encoding.isSome errors.isSome
  | some (.obj (.str cs)) =>
    match encoding with
    | none => throw (.typeError "string argument without an encoding")
    | some (name, codec) =>
      let (encoded, unique) ← match codec with
        | .builtin => do
          let e ← E.lift (encodeStr cs name)
          pure (e, decide (e.length > 1))
        | .py acts res unique => do
          let e ← runCb acts res
          pure (e, unique)
      if unique then
        -- :1031-1038: the encoded object becomes the storage
        E.modify fun h => { h with
          ba := { h.ba with data := seqData encoded, alloc := encoded.length, offset := 0 },
          gen := h.gen + 1 }
      else baIConcatE (.obj (.bytes encoded))
  | some a => do
    encNoArg encoding.isSome errors.isSome
    let counted : Bool ← if a.indexCheck then do
        match ← E.attempt (asSsizeE (some .overflowError) a) with
        | .error e => if isTypeError e then pure false else throw e
        | .ok count =>
          if count < 0 then throw (.valueError "negative count")
          if count > 0 then
            resizeE count
            E.modify fun h => { h with ba := { h.ba with data := List.replicate count.toNat 0 } }
          pure true
      else pure false
    if counted then return ()
    if a.bufferCheck then
      let b ← getBufE a
      match ← E.attempt (resizeE b.len) with
      | .error e =>
        b.rel
        throw e
      | .ok () =>
        let s ← b.read
        E.modify fun h => { h with ba := { h.ba with data := seqData s } }
        b.rel
        return ()
    let slow : E Unit := do
      let (steps, finActs, fin) ←
        getIterE (.typeError s!"cannot convert '{a.typeName}' object to bytearray") a
      initLoopE steps finActs fin (steps.length + 1) 0
    match a with
    | .obj (.list items) | .obj (.tuple items) =>
      resizeE items.length
      let h ← E.get
      match baInitFast h.ba items with
      | .inl (b, none) => E.modify fun h => h.put b
      | .inl (b, some e) => do
        E.modify fun h => h.put b
        throw e
      | .inr () =>
        let size ← curSize
        if size ≠ 0 then resizeE 0
        slow
    | _ => slow

/-! ## Methods that copy -/

/-- `bytearray.translate(table, delete)`, :1709-1796: both buffers are taken before the size is
read; they are released after the copy. -/
def baTranslateE (table : Arg) (deletechars : Option Arg) : E Seq := do
  let vtable ← if table.isNone then pure none else do
    let b ← getBufE table
    if b.len ≠ 256 then
      b.rel
      throw (.valueError "translation table must be 256 characters long")
    pure (some b)
  let relTable : E Unit := match vtable with
    | some b => b.rel
    | none => noRel
  let vdel ← match deletechars with
    | none => pure none
    | some d => do
      match ← E.attempt (getBufE d) with
      | .error e =>
        relTable
        throw e
      | .ok b => pure (some b)
  let relDel : E Unit := match vdel with
    | some b => b.rel
    | none => noRel
  let inlen ← curSize
  match baFromStringAndSize none inlen with
  | .error e =>
    relTable
    relDel
    throw e
  | .ok _ =>
    let input ← curSeq
    let t ← match vtable with
      | some b => some <$> b.read
      | none => pure none
    let del ← match vdel with
      | some b => b.read
      | none => pure []
    let out := match t, del with
      | some t, [] => translateFast input t
      | _, _ => translateSlow input t del
    relTable
    relDel
    return out

/-- `bytearray.split(sep, maxsplit)` (`right = false`), :1868-1900, and `rsplit`, :1992-2024:
`ob_exports` is raised before `sbuf` and `slen` are read and the separator's buffer taken. -/
def baSplitE (rd : Ptr → Int → E Seq) (sep : Option Arg) (maxsplit : Option Arg) (right : Bool) :
    E (List Seq) := do
  let ms ← match maxsplit with
    | none => pure (-1)
    | some a => clinicSsizeE a
  withBufferE fun p n => do
    let sepNone : Bool := match sep with
      | none => true
      | some a => a.isNone
    if sepNone then
      let s ← rd p n
      E.lift ((if right then bytesRSplit else bytesSplit) s none ms)
    else
      let b ← getBufE (sep.getD .me)
      let s ← rd p n
      let t ← b.read
      let r := (if right then bytesRSplit else bytesSplit) s (some t) ms
      b.rel
      E.lift r

/-- `bytearray.partition(sep)` (`right = false`), :1920-1939, and `rpartition`, :1960-1979: the
separator is copied by `_PyByteArray_FromBufferObject`, :148-166 (its `__buffer__` and
`__release_buffer__` both run), and then `self` is read. -/
def baPartitionE (sep : Arg) (right : Bool) : E (Seq × Seq × Seq) := do
  let b ← getBufE sep
  match baFromStringAndSize none b.len with
  | .error e =>
    b.rel
    throw e
  | .ok _ =>
    let t ← b.read
    b.rel
    let s ← curSeq
    E.lift ((if right then stringlibRPartition else stringlibPartition) s t)

/-- The separator of `_Py_strhex_impl`, pystrhex.c:118-150: `PyObject_Length(sep)` runs `__len__`. -/
def hexSepE (sep : Option Arg) : E (Option Nat) := do
  match sep with
  | none => return none
  | some a =>
    let seplen ← lengthE a
    if seplen ≠ 1 then throw (.valueError "sep must be length 1.")
    let c : Nat ← match a with
      | .obj (.str cs) =>
        if cs.headD 0 ≥ 256 then throw (.valueError "sep must be ASCII.")
        pure (cs.headD 0)
      | .obj (.bytes s) | .slen _ _ s => pure (s.headD 0)
      | _ => throw (.typeError "sep must be str or bytes.")
    if c > 127 then throw (.valueError "sep must be ASCII.")
    return some c

/-- `_Py_strhex_impl` past the separator, pystrhex.c:152-253, on the bytes `arg`. -/
def strhexBody (arg : Seq) (parsed : Option Nat) (bytesPerSep : Int) : Py Seq := do
  let group : Int := if parsed.isSome then bytesPerSep else 0
  let sepChar := parsed.getD 0
  let abs : Nat := group.natAbs
  let arglen : Int := arg.length
  let resultlen : Int := if group ≠ 0 ∧ arglen > 0 then Int.tdiv (arglen - 1) abs else 0
  if arglen ≥ Int.tdiv ssizeMax 2 - resultlen then throw memoryError
  let group := if (abs : Int) ≥ arglen then 0 else group
  let abs := if (group = 0) then 0 else abs
  if group = 0 then return arg.flatMap hexPair
  let chunks := (arg.length - 1) / abs
  if group < 0 then return chunkLeft sepChar abs chunks arg
  return chunkRight sepChar abs chunks arg

/-- `bytearray.hex(sep, bytes_per_sep)`, :2733-2747: `argbuf` and `arglen` are read, then
`ob_exports` is raised around `_Py_strhex_with_sep`, whose `PyObject_Length(sep)` can run Python
code (gh-143195); the hexlify loop reads `argbuf` after it. -/
def baHexE (rd : Ptr → Int → E Seq) (sep : Option Arg) (bytesPerSep : Option Arg) : E Seq := do
  let bps ← match bytesPerSep with
    | none => pure 1
    | some a => clinicSsizeE a
  let h ← E.get
  let p := h.ptr
  let arglen := h.ba.size
  exportsUp
  let r ← E.attempt (do
    let parsed ← hexSepE sep
    let arg ← rd p arglen
    E.lift (strhexBody arg parsed bps))
  exportsDown
  E.lift r

/-- `PySequence_Fast(iterable, "can only join an iterable")`. -/
def sequenceFastE (a : Arg) : E (List Item) := do
  match a with
  | .obj o => do
    let xs ← E.lift (sequenceFast (.typeError "can only join an iterable") o)
    return xs.map Item.obj
  | .it steps finActs fin =>
    let rec go : Nat → Nat → List Item → E (List Item)
      | fuel + 1, i, acc => do
        match ← iterStepE steps finActs fin i with
        | none => return acc
        | some (item, j) => go fuel j (acc ++ [item])
      | 0, _, _ => throw .modelFuel
    go (steps.length + 1) 0 []
  | _ => throw (.typeError "can only join an iterable")

def Item.typeName (i : Item) : String := i.toArg.typeName

/-- The pre-pass of `stringlib_bytes_join`, join.h:52-103: an exact `bytes` is used directly,
anything else through `PyObject_GetBuffer`; the buffers taken so far are released on an error. -/
def joinPassE (seplen : Int) : Nat → List Item → Int → List Buf → E (List Buf × Int)
  | _, [], sz, acc => pure (acc, sz)
  | i, item :: rest, sz, acc => do
    let b ← match item with
      | .obj (.bytes s) => pure (⟨.bytes s, noRel⟩ : Buf)
      | _ => do
        match ← E.attempt (getBufE item.toArg) with
        | .ok b => pure b
        | .error _ =>
          for x in acc do x.rel
          throw (.typeError s!"sequence item {i}: expected a bytes-like object, {item.typeName} found")
    let acc := acc ++ [b]
    let itemlen := b.len
    if itemlen > ssizeMax - sz then
      for x in acc do x.rel
      throw (.overflowError "join() result is too long")
    let sz := sz + itemlen
    if i ≠ 0 ∧ seplen > ssizeMax - sz then
      for x in acc do x.rel
      throw (.overflowError "join() result is too long")
    let sz := if i ≠ 0 then sz + seplen else sz
    joinPassE seplen (i + 1) rest sz acc

/-- `bytearray.join(iterable)`, :2630-2639: `ob_exports` of `self` (the separator) is raised around
`stringlib_bytes_join`, join.h:7-170, whose iterator and item buffers can run Python code. -/
def baJoinE (rd : Ptr → Int → E Seq) (iterable : Arg) : E Seq :=
  withBufferE fun _ _ => do
    let items ← sequenceFastE iterable
    -- `sepstr` and `seplen` are read in `bytes_join_lock_held`, after `PySequence_Fast` (join.h:10-11)
    let h ← E.get
    let p := h.ptr
    let n := h.ba.size
    if items.length = 0 then return []
    let (bufs, sz) ← joinPassE n 0 items 0 []
    match baFromStringAndSize none sz with
    | .error e =>
      for x in bufs do x.rel
      throw e
    | .ok _ =>
      let sep ← rd p n
      let parts ← bufs.mapM Buf.read
      for x in bufs do x.rel
      return joinWrite sep parts

/-- `bytearray_richcompare`, :1222-1275: `none` is `NotImplemented`. The sizes are those of the
views; the bytes are compared after the other operand's `__buffer__` ran. Under `-b` a comparison
with `str` warns first; that branch is not modelled (the default configuration). -/
def baRichE (rd : Ptr → Int → E Seq) (other : Arg) (op : CmpOp) : E (Option Bool) := do
  if !other.bufferCheck then return none
  let vs ← getBufE .me
  match ← E.attempt (getBufE other) with
  | .error _ =>
    vs.rel
    return none
  | .ok vo =>
    let selfSize := vs.len
    let otherSize := vo.len
    if selfSize ≠ otherSize ∧ (op = .eq ∨ op = .ne) then
      vs.rel
      vo.rel
      return some (decide (op = .ne))
    let x ← match vs.view with
      | .self p n => rd p n
      | .bytes s => pure s
    let y ← vo.read
    let cmp := memcmp (min x.length y.length) x y
    vs.rel
    vo.rel
    if cmp ≠ 0 then return some (richResult op cmp 0)
    return some (richResult op selfSize otherSize)

end PyLean.BytesObj.Bytes
