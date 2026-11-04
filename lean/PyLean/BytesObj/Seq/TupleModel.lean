import PyLean.RangeSlice.Model
import PyLean.BytesObj.Seq.Elem

/-!
Model of `Objects/tupleobject.c`, CPython 3.15.2 (`Py_GIL_DISABLED` off, 64-bit).

A tuple object is `Tup`: its items, whether its type is exactly `tuple`, the GC
`tracked` flag (visible through `gc.is_tracked`) and the `ob_hash` cache. Objects
that the source returns by identity are distinguished from fresh tuples by
`TRes`, so `t[:] is t` and `() + () is ()` are part of the model's results. The
free lists have no visible effect beyond object identity of dead objects, which
Python code cannot observe, and they are not modelled.
-/

namespace PyLean.BytesObj.Seq

open PyLean
open PyLean.RangeSlice (Slice sliceUnpack adjustIndices toU)

variable {α ρ : Type}

/-- A `PyTupleObject`. `hash` is `ob_hash`, with `-1` for "not computed yet". -/
structure Tup (α : Type) where
  items : List α
  /-- `PyTuple_CheckExact`. -/
  exact : Bool := true
  /-- `_PyObject_GC_IS_TRACKED`. -/
  tracked : Bool := true
  hash : Int := -1
  deriving Repr, DecidableEq

/-- What a tuple-producing function hands back. -/
inductive TRes (α : Type) where
  /-- `Py_NewRef` of an argument: 0 is `self`/`a`, 1 is `b`. -/
  | arg (k : Nat)
  /-- `tuple_get_empty()`, the singleton (tupleobject.c:68-72). -/
  | empty
  | fresh (t : Tup α)
  deriving Repr, DecidableEq

/-- Items of a result, given the arguments. -/
def TRes.items (a b : List α) : TRes α → List α
  | .arg 0 => a
  | .arg _ => b
  | .empty => []
  | .fresh t => t.items

/-- `sizeof(PyTupleObject) - sizeof(PyObject *)`: header, `ob_size`, `ob_hash`. -/
def tupleBase : Int := 32

/-- `tuple_alloc(size)`, tupleobject.c:36-62, for its failure conditions: a
negative size is an internal error and the explicit overflow test raises
`MemoryError`. A free-list hit needs `size - 1 < PyTuple_MAXSAVESIZE`, far below
the overflow bound, so the order of the two does not show. `size != 0` is an
`assert` in the source. -/
def tupleAlloc (size : Int) : Py Unit :=
  if size < 0 then .error systemError
  else if size > (ssizeMax - tupleBase) / 8 then .error memoryError
  else .ok ()

/-! ## Hash -/

/-- `Py_uhash_t` arithmetic is modulo `2^64`. -/
def U64 : Nat := 2 ^ 64

/-- `_PyTuple_HASH_XXPRIME_1`, Include/internal/pycore_tuple.h:66. -/
def XXP1 : Nat := 11400714785074694791
/-- `_PyTuple_HASH_XXPRIME_2`, pycore_tuple.h:67. -/
def XXP2 : Nat := 14029467366897019727
/-- `_PyTuple_HASH_XXPRIME_5`, pycore_tuple.h:68. -/
def XXP5 : Nat := 2870177450012600261

/-- `_PyTuple_HASH_XXROTATE(x)`, pycore_tuple.h:69: `(x << 31) | (x >> 33)` on 64 bits. -/
def xxRotate (x : Nat) : Nat := ((x <<< 31) % U64) ||| (x >>> 33)

/-- The loop body of `tuple_hash`, tupleobject.c:398-400. -/
def hashRound (acc lane : Nat) : Nat :=
  let acc := (acc + lane * XXP2) % U64
  let acc := xxRotate acc
  (acc * XXP1) % U64

/-- `(Py_uhash_t)x` for a `Py_hash_t`. -/
def toUhash (x : Int) : Nat := (x % (U64 : Int)).toNat

/-- `(Py_hash_t)acc` on return. -/
def toHash (acc : Nat) : Int := if acc ≥ 2 ^ 63 then (acc : Int) - U64 else acc

/-- What the caller of `tp_hash` raises when it returns `-1` with no exception set: the result
check of the calling function (`_Py_CheckFunctionResult`, Objects/call.c) turns it into a
`SystemError` whose text names that caller. -/
def hashNoExc : PyExc := .named "SystemError" "~error return without exception set"

/-- The hash loop, tupleobject.c:391-401. `PyObject_Hash` failing is the `.error` case; the C
test is `lane == (Py_uhash_t)-1` (:394), so an element hash of `-1` reported as a success, which
only a broken C `tp_hash` can give (`slot_tp_hash` maps a Python `-1` to `-2`), is a failure too,
with no exception set (`hashNoExc`). -/
def hashLoop (hashE : α → Py Int) : List α → Nat → Py Nat
  | [], acc => .ok acc
  | x :: xs, acc =>
    match hashE x with
    | .ok lane =>
      if toUhash lane = U64 - 1 then .error hashNoExc
      else hashLoop hashE xs (hashRound acc (toUhash lane))
    | .error e => .error e

/-- `acc += len ^ (_PyTuple_HASH_XXPRIME_5 ^ 3527539UL)` and the `-1` remap,
tupleobject.c:405-409. -/
def hashFinish (acc len : Nat) : Nat :=
  let acc := (acc + (len ^^^ (XXP5 ^^^ 3527539))) % U64
  if acc = U64 - 1 then 1546275796 else acc

/-- `tuple_hash(op)`, tupleobject.c:371-414: the cached value when there is one,
otherwise the xxHash-style loop, and the cache is written on success only. -/
def tupleHash (hashE : α → Py Int) (t : Tup α) : Py (Int × Tup α) :=
  if toUhash t.hash ≠ U64 - 1 then .ok (t.hash, t)
  else
    match hashLoop hashE t.items XXP5 with
    | .ok acc =>
      let h := toHash (hashFinish acc t.items.length)
      .ok (h, { t with hash := h })
    | .error e => .error e

/-- `tuple_hash`, tupleobject.c:371-414, with the stack test: `stackFull` is
`_Py_EnterRecursiveCall(" while hashing a tuple")` failing (:387), which comes after the cache, so a
cached tuple never fails it. The text is `"Stack overflow (used %d kB)%s"` (Python/ceval.c:328-331),
which embeds the stack used. -/
def tupleHashGuarded (hashE : α → Py Int) (t : Tup α) (stackFull : Bool) : Py (Int × Tup α) :=
  if toUhash t.hash ≠ U64 - 1 then .ok (t.hash, t)
  else if stackFull then
    .error (.named "RecursionError" "~Stack overflow (used %d kB) while hashing a tuple")
  else tupleHash hashE t

/-! ## Item access -/

/-- `tuple_length(self)`, tupleobject.c:416-421: `Py_SIZE`. -/
def tupleLength (a : List α) : Int := a.length

/-- `tuple_contains(self, el)`, tupleobject.c:423-432: `item == el`, item on the left. -/
def tupleContains (E : ElemOps α ρ) (el : α) : List α → Py Bool
  | [] => .ok false
  | x :: xs =>
    match richBool E .eq x el with
    | .ok false => tupleContains E el xs
    | r => r

/-- `tuple_item(op, i)`, tupleobject.c:434-443. -/
def tupleItem (a : List α) (i : Int) : Py α :=
  if i < 0 ∨ i ≥ a.length then .error (.indexError "tuple index out of range")
  else match slot a i with
    | some v => .ok v
    | none => .error (cUB "read outside the items array")

/-- `PyTuple_FromArray(src, n)`, tupleobject.c:445-469: untracked unless an item
may be tracked (`maybe_tracked`, :165-169). -/
def tupleFromArray (mayTrack : α → Bool) (src : List α) : Py (TRes α) :=
  if src.length = 0 then .ok .empty
  else
    match tupleAlloc src.length with
    | .ok () => .ok (.fresh { items := src, tracked := src.any mayTrack })
    | .error e => .error e

/-- `_PyTuple_FromStackRefStealOnSuccess`, tupleobject.c:471-494: as above. -/
def tupleFromStackRef (mayTrack : α → Bool) (src : List α) : Py (TRes α) :=
  tupleFromArray mayTrack src

/-- `_PyTuple_FromArraySteal(src, n)`, tupleobject.c:496-516: always tracked. -/
def tupleFromArraySteal (src : List α) : Py (TRes α) :=
  if src.length = 0 then .ok .empty
  else
    match tupleAlloc src.length with
    | .ok () => .ok (.fresh { items := src, tracked := true })
    | .error e => .error e

/-- `PyTuple_Pack(n, ...)`, tupleobject.c:171-203. -/
def tuplePack (mayTrack : α → Bool) (n : Int) (args : List α) : Py (TRes α) :=
  if n = 0 then .ok .empty
  else
    match tupleAlloc n with
    | .ok () => .ok (.fresh { items := args, tracked := args.any mayTrack })
    | .error e => .error e

/-- `_PyTuple_FromPairSteal(first, second)`, tupleobject.c:214-233, and `_PyTuple_FromPair`, :205-212. -/
def tupleFromPair (mayTrack : α → Bool) (first second : α) : Py (TRes α) :=
  match tupleAlloc 2 with
  | .ok () => .ok (.fresh { items := [first, second], tracked := mayTrack first || mayTrack second })
  | .error e => .error e

/-- `_PyTuple_MaybeUntrack(op)`, tupleobject.c:137-157, run by the collector.
`mayBeTracked` is `_PyObject_GC_MAY_BE_TRACKED`; `NULL` items are `none`. -/
def tupleMaybeUntrack (mayBeTracked : α → Bool) (exact : Bool) (tracked : Bool)
    (items : List (Option α)) : Bool :=
  if !exact || !tracked then tracked
  else if items.any (fun e => match e with | none => true | some x => mayBeTracked x) then tracked
  else false

/-- `tuple_slice(a, ilow, ihigh)`, tupleobject.c:518-532: `ilow` clamped below at 0, `ihigh` above
at the size and below at `ilow` (:522-527), the tuple itself for the whole of an exact tuple
(:528-530), otherwise `PyTuple_FromArray` of the range (:531). -/
def tupleSlice (mayTrack : α → Bool) (a : Tup α) (ilow ihigh : Int) : Py (TRes α) :=
  let n : Int := a.items.length
  let ilow := if ilow < 0 then 0 else ilow
  let ihigh := if ihigh > n then n else ihigh
  let ihigh := if ihigh < ilow then ilow else ihigh
  if ilow = 0 ∧ ihigh = n ∧ a.exact then .ok (.arg 0)
  else tupleFromArray mayTrack ((a.items.drop ilow.toNat).take (ihigh - ilow).toNat)

/-- `PyTuple_GetSlice(op, i, j)`, tupleobject.c:553-561. `none` is a non-tuple or `NULL`. -/
def pyTupleGetSlice (mayTrack : α → Bool) (op : Option (Tup α)) (i j : Int) : Py (TRes α) :=
  match op with
  | none => .error systemError
  | some a => tupleSlice mayTrack a i j

/-- The right operand of `tuple + other`. -/
inductive ConcatArg (α : Type) where
  | tuple (t : Tup α)
  | other (typeName : String)

/-- `_PyTuple_Concat(aa, bb)`, tupleobject.c:563-608. -/
def tupleConcat (a : Tup α) (bb : ConcatArg α) : Py (TRes α) :=
  let exactB : Bool := match bb with | .tuple t => t.exact | .other _ => false
  if a.items.length = 0 ∧ exactB then .ok (.arg 1)
  else
    match bb with
    | .other name =>
      .error (.typeError s!"can only concatenate tuple (not \"{trunc200 name}\") to tuple")
    | .tuple b =>
      if b.items.length = 0 ∧ a.exact then .ok (.arg 0)
      else
        let size : Int := a.items.length + b.items.length
        if size = 0 then .ok .empty
        else
          match tupleAlloc size with
          | .ok () => .ok (.fresh { items := a.items ++ b.items, tracked := true })
          | .error e => .error e

/-- `tuple_repeat(self, n)`, tupleobject.c:610-657. -/
def tupleRepeat (a : Tup α) (n : Int) : Py (TRes α) :=
  let inputSize : Int := a.items.length
  if (inputSize = 0 ∨ n = 1) ∧ a.exact then .ok (.arg 0)
  else if inputSize = 0 ∨ n ≤ 0 then .ok .empty
  else if inputSize > ssizeMax / n then .error memoryError
  else
    match tupleAlloc (inputSize * n) with
    | .ok () => .ok (.fresh { items := (List.replicate n.toNat a.items).flatten, tracked := true })
    | .error e => .error e

/-- `sequence_repeat` conversion of the count, then `tuple_repeat`. -/
def tupleMul (a : Tup α) (n : Int) : Py (TRes α) := do
  let n ← PyLean.Sequences.repeatCount n
  tupleRepeat a n

/-- The search loop of `tuple_index_impl`, tupleobject.c:690-696. `xs` is the
tail of the items from `i` on, `stop` the (clipped) bound. -/
def tupleIndexLoop (E : ElemOps α ρ) (value : α) (stop : Int) : List α → Int → Py (Option Int)
  | [], _ => .ok none
  | x :: xs, i =>
    if i < stop then
      match richBool E .eq x value with
      | .ok true => .ok (some i)
      | .ok false => tupleIndexLoop E value stop xs (i + 1)
      | .error e => .error e
    else .ok none

/-- `start` and `stop` of `tuple_index_impl`, tupleobject.c:679-689, after the
`slice_index(accept={int})` conversions (saturating). -/
def tupleIndexBounds (n : Int) (start stop : Option Int) : Int × Int :=
  let start := PyLean.Sequences.sliceIndex (start.getD 0)
  let stop := PyLean.Sequences.sliceIndex (stop.getD ssizeMax)
  let start := if start < 0 then (if start + n < 0 then 0 else start + n) else start
  let stop := if stop < 0 then stop + n else if stop > n then n else stop
  (start, stop)

/-- `t.index(value, start, stop)`, `tuple_index_impl`, tupleobject.c:672-699. -/
def tupleIndex (E : ElemOps α ρ) (t : List α) (value : α) (start stop : Option Int) : Py Int :=
  let (start, stop) := tupleIndexBounds t.length start stop
  match tupleIndexLoop E value stop (t.drop start.toNat) start with
  | .ok (some i) => .ok i
  | .ok none => .error (.valueError "tuple.index(x): x not in tuple")
  | .error e => .error e

/-- `t.count(value)`, `tuple_count_impl`, tupleobject.c:710-725. -/
def tupleCount (E : ElemOps α ρ) (value : α) : List α → Int → Py Int
  | [], count => .ok count
  | x :: xs, count =>
    match richBool E .eq x value with
    | .ok true => tupleCount E value xs (count + 1)
    | .ok false => tupleCount E value xs count
    | .error e => .error e

/-! ## Rich comparison -/

/-- The search of `tuple_richcompare`, tupleobject.c:764-771: the first pair that
is not equal, or `none` when one side runs out. -/
def tupleFirstDiff (E : ElemOps α ρ) : List α → List α → Py (Option (α × α))
  | x :: xs, y :: ys =>
    match richBool E .eq x y with
    | .ok true => tupleFirstDiff E xs ys
    | .ok false => .ok (some (x, y))
    | .error e => .error e
  | _, _ => .ok none

/-- `tuple_richcompare(v, w, op)`, tupleobject.c:737-788. `NotImplemented` for a
non-tuple operand is handled by the caller. -/
def tupleRichcompare (E : ElemOps α ρ) (op : CmpOp) (v w : List α) : Py ρ :=
  match tupleFirstDiff E v w with
  | .error e => .error e
  | .ok none => .ok (E.ofBool (cmpSizes op v.length w.length))
  | .ok (some (x, y)) =>
    if op = .eq then .ok (E.ofBool false)
    else if op = .ne then .ok (E.ofBool true)
    else E.rich op x y

/-! ## Subscript -/

/-- `tuple_subscript(op, item)` for an int item, tupleobject.c:904-910. -/
def tupleGetItem (a : List α) (i : Int) : Py α := do
  let i ← PyLean.Sequences.subIndex i
  let i := if i < 0 then i + a.length else i
  tupleItem a i

/-- `tuple_subscript(op, item)` for a slice, tupleobject.c:912-946. -/
def tupleGetSlice (a : Tup α) (s : Slice) : Py (TRes α) := do
  let (start, stop, step) ← sliceUnpack s
  let (start, _, slicelength) := adjustIndices a.items.length start stop step
  if slicelength ≤ 0 then .ok .empty
  else if start = 0 ∧ step = 1 ∧ slicelength = a.items.length ∧ a.exact then .ok (.arg 0)
  else
    match tupleAlloc slicelength with
    | .ok () =>
      match sliceLoop a.items (toU step) slicelength.toNat (toU start) with
      | .ok r => .ok (.fresh { items := r, tracked := true })
      | .error e => .error e
    | .error e => .error e

/-- `_PyEval_UnpackIndices`, Python/ceval.c, for an exact list or tuple under `BINARY_SLICE`: each
index through `_PyEval_SliceIndex`, which clamps, then `PySlice_AdjustIndices(len, ..., 1)`. -/
def unpackIndices (len : Int) (s : Slice) : Int × Int :=
  let a := match s.start with | none => 0 | some v => RangeSlice.clampSsize v
  let b := match s.stop with | none => ssizeMax | some v => RangeSlice.clampSsize v
  let (a, b, _) := adjustIndices len a b 1
  (a, b)

/-- `_PyTuple_BinarySlice(container, start, stop)`, tupleobject.c:534-551, for an exact tuple. -/
def tupleBinarySlice (mayTrack : α → Bool) (t : Tup α) (s : Slice) : Py (TRes α) :=
  let len : Int := t.items.length
  let (istart, istop) := unpackIndices len s
  if istart = 0 ∧ istop = len then .ok (.arg 0)
  else
    let istop := if istop < istart then istart else istop
    tupleFromArray mayTrack ((t.items.drop istart.toNat).take (istop - istart).toNat)

/-- `tuple_iteritem(obj, index)`, tupleobject.c:889-898: the `_tp_iteritem` of a `for` loop. -/
def tupleIterItem (t : List α) (index : Int) : Option α × Int :=
  if index ≥ t.length then (none, index) else (slot t index, index + 1)

/-! ## C API -/

/-- `PyTuple_New(size)`, tupleobject.c:74-90: the singleton for size 0 (:78-80), before `tuple_alloc`
refuses a negative size or one past `tupleLimit` (:81-84); otherwise `NULL` items, tracked, with no
cached hash (`_PyTuple_RESET_HASH_CACHE` in `tuple_alloc`). -/
def pyTupleNew (size : Int) : Py (TRes (Option α)) :=
  if size = 0 then .ok .empty
  else
    match tupleAlloc size with
    | .ok () => .ok (.fresh { items := List.replicate size.toNat none, tracked := true })
    | .error e => .error e

/-- `PyTuple_Size(op)`, tupleobject.c:92-101. `none` is a non-tuple. -/
def pyTupleSize (op : Option (List α)) : Py Int :=
  match op with
  | none => .error systemError
  | some a => .ok a.length

/-- `PyTuple_GetItem(op, i)`, tupleobject.c:103-115. -/
def pyTupleGetItem (op : Option (List α)) (i : Int) : Py α :=
  match op with
  | none => .error systemError
  | some a =>
    if i < 0 ∨ i ≥ a.length then .error (.indexError "tuple index out of range")
    else match slot a i with
      | some v => .ok v
      | none => .error (cUB "read outside the items array")

/-- `PyTuple_SetItem(op, i, newitem)`, tupleobject.c:117-135. `none` is an object that is not a
tuple (`PyTuple_Check`, so a subclass instance is `some`); `unique` is
`_PyObject_IsUniquelyReferenced(op)`, tested in the same condition, so both refusals are the one
`SystemError` (:121-125). Then the index test (:126-131) and `Py_XSETREF` of the slot (:132-133), and
nothing else: `ob_hash` keeps a hash computed before, as do the type and the GC flag. `newitem` may be
`NULL`, an `Option` element type's `none`. -/
def pyTupleSetItem (op : Option (Tup α)) (unique : Bool) (i : Int) (v : α) : Py (Tup α) :=
  match op with
  | none => .error systemError
  | some t =>
    if !unique then .error systemError
    else if i < 0 ∨ i ≥ t.items.length then .error (.indexError "tuple assignment index out of range")
    else .ok { t with items := t.items.set i.toNat v }

/-- `_PyTuple_Resize(pv, newsize)`, tupleobject.c:1045-1123, on the object `*pv`: `none` is `NULL`,
and `exact` is `Py_IS_TYPE(v, &PyTuple_Type)` (:1054), so an object of any other type, a subclass
instance included, has `exact = false`. `unique` is `_PyObject_IsUniquelyReferenced(*pv)`, which is
not asked of an empty tuple, the shared singleton (:1055). The refusals of :1054-1059 are one
`SystemError`. Then, in order: the same size leaves `*pv` as it is (`.arg 0`, :1063-1065); size 0
makes `*pv` the singleton (:1066-1070); the empty tuple is never resized in place but replaced by
`PyTuple_New(newsize)` (:1071-1080); a size past what `tuple_alloc` can give is `MemoryError`
(:1081-1088); otherwise the object is reallocated (`PyObject_GC_Resize`, :1101), the items past
`newsize` dropped (:1097-1099), the new slots `NULL` (:1117-1119), and it is tracked again (:1121),
with `ob_hash` as it was, since nothing resets it. That object, which `*pv` now points to, is the
`.fresh` result. A failed reallocation is out of memory, outside the model. -/
def tupleResize (v : Option (Tup (Option α))) (unique : Bool) (newsize : Int) :
    Py (TRes (Option α)) :=
  match v with
  | none => .error systemError
  | some t =>
    let oldsize : Int := t.items.length
    if !t.exact || newsize < 0 || (oldsize ≠ 0 && !unique) then .error systemError
    else if oldsize = newsize then .ok (.arg 0)
    else if newsize = 0 then .ok .empty
    else if oldsize = 0 then pyTupleNew newsize
    else if newsize > (ssizeMax - tupleBase) / 8 then .error memoryError
    else .ok (.fresh { t with items := t.items.take newsize.toNat ++
                                List.replicate (newsize - oldsize).toNat none, tracked := true })

/-! ## Iterator -/

/-- `_PyTupleIterObject`: `it_seq` is cleared when exhausted. -/
structure TupleIter (α : Type) where
  index : Int
  seq : Option (List α)
  deriving Repr, DecidableEq

/-- `tuple_iter(seq)`, tupleobject.c:1276-1293. -/
def tupleIter (t : List α) : TupleIter α := ⟨0, some t⟩

/-- `tupleiter_next(self)`, tupleobject.c:1147-1174. -/
def tupleIterNext (it : TupleIter α) : Option α × TupleIter α :=
  match it.seq with
  | none => (none, it)
  | some s =>
    if it.index < s.length then (slot s it.index, { it with index := it.index + 1 })
    else (none, { it with seq := none })

/-- `tupleiter_len(self)`, tupleobject.c:1176-1191. -/
def tupleIterLen (it : TupleIter α) : Int :=
  match it.seq with
  | some s => (s.length : Int) - it.index
  | none => 0

/-- The value of `it.__reduce__()`: `(callable, (it_seq,), index)` for a live iterator
(`Py_BuildValue("N(O)n", ...)`, tupleobject.c:1210-1211) and `(callable, ((),))` for an exhausted one
(`"N(())"`, :1213). -/
inductive TIterReduce (β α : Type) where
  | live (callable : β) (seq : List α) (index : Int)
  | empty (callable : β)
  deriving Repr, DecidableEq

/-- `tupleiter_reduce(self)`, tupleobject.c:1195-1214. `getBuiltin it` is
`_PyEval_GetBuiltin(&_Py_ID(iter))` (Python/ceval.c), a lookup in the frame's builtins that can run
user code (a key's `__eq__`) which may advance or exhaust this very iterator, and that fails with
`AttributeError("iter")` when the name is missing. The lookup comes first ("call must be before access
of iterator pointers", gh-101765, :1198-1203); `it_seq` and `it_index` are then read from the iterator
as the lookup left it (:1210-1213). A failed lookup hands `NULL` to `N`, so `Py_BuildValue` returns
`NULL` with the lookup's exception. -/
def tupleIterReduce {β : Type} (getBuiltin : TupleIter α → Py β × TupleIter α) (it : TupleIter α) :
    Py (TIterReduce β α) × TupleIter α :=
  match getBuiltin it with
  | (.error e, it') => (.error e, it')
  | (.ok c, it') =>
    match it'.seq with
    | some s => (.ok (.live c s it'.index), it')
    | none => (.ok (.empty c), it')

/-- `tupleiter_setstate(self, state)`, tupleobject.c:1216-1231, for an int `state`: `PyLong_AsSsize_t`
(:1220-1222) refuses one outside `Py_ssize_t` with `OverflowError`; a live iterator takes the index
clipped to `[0, len]` (:1223-1228), an exhausted one is left alone. -/
def tupleIterSetstate (it : TupleIter α) (state : Int) : Py (TupleIter α) := do
  let index ← PyLean.Sequences.asSsize state
  match it.seq with
  | some s =>
    let index := if index < 0 then 0 else if index > s.length then (s.length : Int) else index
    .ok { it with index := index }
  | none => .ok it

/-- `tupleiter_setstate(self, state)` for any object: `PyLong_AsSsize_t(state)` refuses one that is
not an int (`none`) with `TypeError("an integer is required")` (Objects/longobject.c:717-719), before
the iterator is looked at. -/
def tupleIterSetstateObj (it : TupleIter α) : Option Int → Py (TupleIter α)
  | none => .error (.typeError "an integer is required")
  | some s => tupleIterSetstate it s

/-- Unpickling a `__reduce__` value whose callable is `iter`: `iter(seq)`, then `__setstate__(index)`
for the live form; `iter(())` for the exhausted one. -/
def tupleIterRebuild {β : Type} : TIterReduce β α → Py (TupleIter α)
  | .live _ s i => tupleIterSetstate (tupleIter s) i
  | .empty _ => .ok (tupleIter [])

end PyLean.BytesObj.Seq
