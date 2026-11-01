import PyLean.RangeSlice.Model
import PyLean.BytesObj.Seq.Elem

/-!
Model of `Objects/tupleobject.c`, CPython 3.14.7 (`Py_GIL_DISABLED` off, 64-bit).

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

/-- The hash loop, tupleobject.c:392-401. `PyObject_Hash` failing is the `.error`
case (`lane == (Py_uhash_t)-1`). -/
def hashLoop (hashE : α → Py Int) : List α → Nat → Py Nat
  | [], acc => .ok acc
  | x :: xs, acc =>
    match hashE x with
    | .ok lane => hashLoop hashE xs (hashRound acc (toUhash lane))
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

/-- `_PyTuple_FromArray(src, n)`, tupleobject.c:445-469: untracked unless an item
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

/-- `_PyTuple_MaybeUntrack(op)`, tupleobject.c:137-157, run by the collector.
`mayBeTracked` is `_PyObject_GC_MAY_BE_TRACKED`; `NULL` items are `none`. -/
def tupleMaybeUntrack (mayBeTracked : α → Bool) (exact : Bool) (tracked : Bool)
    (items : List (Option α)) : Bool :=
  if !exact || !tracked then tracked
  else if items.any (fun e => match e with | none => true | some x => mayBeTracked x) then tracked
  else false

/-- `tuple_slice(a, ilow, ihigh)`, tupleobject.c:518-551. -/
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

/-- `tuple_concat(aa, bb)`, tupleobject.c@3.14.7:485-530. -/
def tupleConcat (a : Tup α) (bb : ConcatArg α) : Py (TRes α) :=
  let exactB : Bool := match bb with | .tuple t => t.exact | .other _ => false
  if a.items.length = 0 ∧ exactB then .ok (.arg 1)
  else
    match bb with
    | .other name =>
      .error (.typeError s!"can only concatenate tuple (not \"{name}\") to tuple")
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

/-! ## Construction -/

/-- `PySequence_Tuple(v)` on a sequence argument (Objects/abstract.c:2005-2079), with
`tuple_new_impl` and `tuple_vectorcall`. The argument is what the type does:
an exact tuple is returned, a list goes through `PyList_AsTuple`
(`_PyTuple_FromArray`), other iterables through a buffer or a list and
`_PyTuple_FromArraySteal`. -/
inductive TupleSrc (α : Type) where
  | exactTuple (t : Tup α)
  | exactList (l : List α)
  | iterable (items : List α)

def pySequenceTuple (mayTrack : α → Bool) : TupleSrc α → Py (TRes α)
  | .exactTuple _ => .ok (.arg 0)
  | .exactList l => tupleFromArray mayTrack l
  | .iterable items => tupleFromArraySteal items

/-- `tuple_new_impl(type, iterable)`, tupleobject.c:807-820 for `type == tuple`. -/
def tupleNew (mayTrack : α → Bool) (iterable : Option (TupleSrc α)) : Py (TRes α) :=
  match iterable with
  | none => .ok .empty
  | some src => pySequenceTuple mayTrack src

/-- `tuple_subtype_new(type, iterable)`, tupleobject.c:843-876: a fresh subclass
instance holding the items of `tuple(iterable)`, tracked, with no cached hash. -/
def tupleSubtypeNew (mayTrack : α → Bool) (iterable : Option (TupleSrc α)) : Py (Tup α) :=
  let items := fun (r : TRes α) (src : Option (TupleSrc α)) =>
    match src with
    | some (.exactTuple t) => r.items t.items []
    | _ => r.items [] []
  match tupleNew mayTrack iterable with
  | .ok r => .ok { items := items r iterable, exact := false, tracked := true, hash := -1 }
  | .error e => .error e

/-- `tuple_vectorcall(type, args, nargsf, kwnames)`, tupleobject.c:822-841:
keyword names and the argument count are checked in that order. -/
def tupleVectorcall (mayTrack : α → Bool) (args : List (TupleSrc α)) (nkw : Nat) : Py (TRes α) :=
  if nkw ≠ 0 then .error (.typeError "tuple() takes no keyword arguments")
  else if args.length > 1 then
    .error (.typeError s!"tuple expected at most 1 argument, got {args.length}")
  else
    match args with
    | src :: _ => tupleNew mayTrack (some src)
    | [] => .ok .empty

/-- `tuple.__getnewargs__`, tupleobject.c:960-965: `(tuple_slice(self, 0, n),)`. -/
def tupleGetnewargs (mayTrack : α → Bool) (a : Tup α) : Py (TRes α) :=
  tupleSlice mayTrack a 0 a.items.length

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

/-! ## C API -/

/-- `PyTuple_New(size)`, tupleobject.c:74-90: `NULL` items, tracked. -/
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

/-- `PyTuple_SetItem(op, i, newitem)`, tupleobject.c:117-135; `unique` is
`_PyObject_IsUniquelyReferenced(op)`. The cached hash is not reset. -/
def pyTupleSetItem (op : Option (List α)) (unique : Bool) (i : Int) (v : α) : Py (List α) :=
  match op with
  | none => .error systemError
  | some a =>
    if !unique then .error systemError
    else if i < 0 ∨ i ≥ a.length then .error (.indexError "tuple assignment index out of range")
    else .ok (a.set i.toNat v)

/-- `_PyTuple_Resize(pv, newsize)`, tupleobject.c:1045-1123, on the items. The
checks on line 964 fail with an internal error; `NULL` items pad a growing tuple
(`memset`, :1118). A negative `newsize` runs the `Py_CLEAR` loop of :1097 from
`ob_item[newsize]`, outside the object. -/
def tupleResize (v : Option (List (Option α))) (isExact unique : Bool) (newsize : Int) :
    Py (List (Option α)) :=
  match v with
  | none => .error systemError
  | some items =>
    let oldsize : Int := items.length
    if !isExact || (oldsize ≠ 0 && !unique) then .error systemError
    else if oldsize = newsize then .ok items
    else if newsize = 0 then .ok []
    else if oldsize = 0 then
      match tupleAlloc newsize with
      | .ok () => .ok (List.replicate newsize.toNat none)
      | .error e => .error e
    else if newsize < 0 then .error (cUB "_PyTuple_Resize with a negative size")
    else .ok (items.take newsize.toNat ++ List.replicate (newsize - oldsize).toNat none)

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

/-- `tupleiter_reduce(self)`, tupleobject.c:1195-1214, as `(args, state)`:
`iter(seq)` plus the index, or `iter(())` when exhausted. -/
def tupleIterReduce (it : TupleIter α) : List α × Option Int :=
  match it.seq with
  | some s => (s, some it.index)
  | none => ([], none)

/-- `tupleiter_setstate(self, state)`, tupleobject.c:1216-1231. -/
def tupleIterSetstate (it : TupleIter α) (state : Int) : Py (TupleIter α) := do
  let index ← PyLean.Sequences.asSsize state
  match it.seq with
  | some s =>
    let index := if index < 0 then 0 else if index > s.length then (s.length : Int) else index
    .ok { it with index := index }
  | none => .ok it

/-- Rebuild from `__reduce__`: `iter(args)`, then `__setstate__(state)`. -/
def tupleIterRebuild (r : List α × Option Int) : Py (TupleIter α) :=
  match r.2 with
  | some st => tupleIterSetstate (tupleIter r.1) st
  | none => .ok (tupleIter r.1)

end PyLean.BytesObj.Seq
