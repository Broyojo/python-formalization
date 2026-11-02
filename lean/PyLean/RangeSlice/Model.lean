import PyLean.Core

/-!
Model of the C builtins `range` (`Objects/rangeobject.c`) and `slice`
(`Objects/sliceobject.c`) of CPython 3.15.2, plus the two `listobject.c`
functions that consume `PySlice_Unpack`/`PySlice_AdjustIndices`. The critical
sections 3.15 put around the iterator methods do not change what one thread sees,
and free-threaded builds are out of scope.

Scope and conventions:

* LP64: `long`, `Py_ssize_t` and `size_t` are 64 bits (macOS/Linux builds).
* Python ints are `Int`. A C `long` is an `Int` in `[longMin, longMax]`;
  unsigned long values are `Int`s in `[0, 2^64)` produced by `toU`, and the
  unsigned operations `uadd`/`usub`/`umul` reduce mod `2^64` exactly as C does.
  CPython is compiled with `-fno-strict-overflow` (configure.ac:2255-2281),
  so signed `long` arithmetic that could overflow is modelled with `wrap`
  (two's complement); the properties show where that never happens.
* Range arguments and slice parts are exact ints (or `None` for slice parts):
  `PyNumber_Index` returns exact ints (Objects/abstract.c), so this is what
  every `rangeobject` holds. Objects that are not ints are out of scope.
* A range object is created only through `makeRangeObject`, which stores
  `compute_range_length` in the `length` field, as `make_range_object` does.
-/

namespace PyLean.RangeSlice

open PyLean

/-! ## C integer helpers -/

def two64 : Int := 18446744073709551616
def longMin : Int := -9223372036854775808
def longMax : Int := 9223372036854775807

/-- `x` fits in a C `long`. -/
def IsLong (x : Int) : Prop := longMin ≤ x ∧ x ≤ longMax

instance (x : Int) : Decidable (IsLong x) := inferInstanceAs (Decidable (_ ∧ _))

/-- `(unsigned long)x`. -/
def toU (x : Int) : Int := x % two64

/-- Unsigned long `a + b`, `a - b`, `a * b` (wrapping mod `2^64`). -/
def uadd (a b : Int) : Int := (a + b) % two64
def usub (a b : Int) : Int := (a - b) % two64
def umul (a b : Int) : Int := (a * b) % two64

/-- `(long)x` and signed `long` arithmetic under `-fno-strict-overflow`:
two's complement wraparound. -/
def wrap (x : Int) : Int :=
  if x % two64 > longMax then x % two64 - two64 else x % two64

/-- `PyLong_AsLongAndOverflow` / `PyLong_AsLong` on an exact int: `none`
is the overflow case (`overflow != 0`, resp. `OverflowError` set). -/
def asLong (x : Int) : Option Int := if IsLong x then some x else none

/-! ## Range objects -/

/-- `rangeobject`, rangeobject.c:35-41. All four fields are PyLongs. -/
structure Range where
  start : Int
  stop : Int
  step : Int
  length : Int
  deriving Repr, DecidableEq, Inhabited

/-- `get_len_of_range`, rangeobject.c:991-1013, in unsigned long arithmetic.
`hi - 1UL - lo` converts `hi` and `lo` to unsigned long; `/ step` converts
`step` to unsigned long. -/
def getLenOfRange (lo hi step : Int) : Int :=
  if step > 0 ∧ lo < hi then
    uadd 1 (usub (usub (toU hi) 1) (toU lo) / toU step)
  else if step < 0 ∧ lo > hi then
    uadd 1 (usub (usub (toU lo) 1) (toU hi) / usub 0 (toU step))
  else 0

/-- `compute_range_length_long`, rangeobject.c:202-236. `none` is the
`-2` ("overflow") return; the `-1` error return cannot happen for ints. -/
def computeRangeLengthLong (start stop step : Int) : Option Int := do
  let lstart ← asLong start
  let lstop ← asLong stop
  let lstep ← asLong step
  let ulen := getLenOfRange lstart lstop lstep
  if ulen > longMax then none else some ulen

/-- The PyLong part of `compute_range_length`, rangeobject.c:264-313:
`(lo, hi, step)` is `(start, stop, step)` for a positive step and
`(stop, start, -step)` otherwise; then `0` if `lo >= hi`, else
`(hi - lo - 1) // step + 1`. `PyNumber_FloorDivide` by the positive step is
`Int.ediv`. (A zero step never reaches this function: `validate_step` rejects
it and slicing multiplies two non-zero steps.) -/
def computeRangeLengthSlow (start stop step : Int) : Int :=
  if step > 0 then (if start ≥ stop then 0 else (stop - start - 1) / step + 1)
  else (if stop ≥ start then 0 else (start - stop - 1) / (-step) + 1)

/-- `compute_range_length`, rangeobject.c:243-314: the `long` fast path,
then the PyLong slow path. -/
def computeRangeLength (start stop step : Int) : Int :=
  match computeRangeLengthLong start stop step with
  | some len => len
  | none => computeRangeLengthSlow start stop step

/-- `make_range_object`, rangeobject.c:66-88. -/
def makeRangeObject (start stop step : Int) : Range :=
  ⟨start, stop, step, computeRangeLength start stop step⟩

/-- `validate_step`, rangeobject.c:46-61. `none` is an omitted step. -/
def validateStep : Option Int → Py Int
  | none => .ok 1
  | some s => if s = 0 then .error (.valueError "range() arg 3 must not be zero") else .ok s

/-- `range(start, stop[, step])`, `range_from_array` cases 3 and 2,
rangeobject.c:103-124 and :139. -/
def rangeNew (start stop : Int) (step : Option Int) : Py Range := do
  let st ← validateStep step
  return makeRangeObject start stop st

/-- `range(stop)`, `range_from_array` case 1, rangeobject.c:125-132. -/
def range1 (stop : Int) : Range := makeRangeObject 0 stop 1

/-- `PyLong_AsSsize_t` overflow message, Objects/longobject.c:748. -/
def ssizeOverflow : PyExc := .overflowError "Python int too large to convert to C ssize_t"

/-- `len(r)`: `range_length`, rangeobject.c:325-330 (`PyLong_AsSsize_t`). -/
def rangeLength (r : Range) : Py Int :=
  if r.length ≤ ssizeMax then .ok r.length else .error ssizeOverflow

/-- `compute_item`, rangeobject.c:332-351: `start + i * step` (the
`step == 1` branch skips the multiplication). -/
def computeItem (r : Range) (i : Int) : Int :=
  if r.step = 1 then r.start + i else r.start + i * r.step

/-- `compute_range_item`, rangeobject.c:353-404; `r[i]` for an int `i`
(`range_subscript`, :729-739). -/
def computeRangeItem (r : Range) (arg : Int) : Py Int :=
  let i := if arg < 0 then r.length + arg else arg
  if i < 0 ∨ i ≥ r.length then .error (.indexError "range object index out of range")
  else .ok (computeItem r i)

/-! ## Slice objects -/

/-- A slice whose parts are ints or `None`. -/
structure Slice where
  start : Option Int
  stop : Option Int
  step : Option Int
  deriving Repr, DecidableEq, Inhabited

/-- The start/stop clipping block of `_PySlice_GetLongIndices`,
sliceobject.c:444-467 (start) and :469-492 (stop). -/
def clipLong (v : Option Int) (dflt lower upper length : Int) : Int :=
  match v with
  | none => dflt
  | some x =>
    if x < 0 then
      let y := x + length
      if y < lower then lower else y
    else if x > upper then upper else x

/-- `_PySlice_GetLongIndices`, sliceobject.c:396-513, all PyLong. -/
def getLongIndices (s : Slice) (length : Int) : Py (Int × Int × Int) := do
  let (step, neg) ← match s.step with
    | none => pure (1, false)
    | some st =>
      if st = 0 then throw (.valueError "slice step cannot be zero") else pure (st, decide (st < 0))
  let (lower, upper) := if neg then ((-1 : Int), length + -1) else (0, length)
  let start := clipLong s.start (if neg then upper else lower) lower upper length
  let stop := clipLong s.stop (if neg then lower else upper) lower upper length
  return (start, stop, step)

/-- `slice.indices(length)`, `slice_indices`, sliceobject.c:527-552. -/
def sliceIndices (s : Slice) (length : Int) : Py (Int × Int × Int) :=
  if length < 0 then .error (.valueError "length should not be negative")
  else getLongIndices s length

/-- `r[s]`: `compute_slice`, rangeobject.c:418-455. -/
def computeSlice (r : Range) (s : Slice) : Py Range := do
  let (start, stop, step) ← getLongIndices s r.length
  let substep := r.step * step
  return makeRangeObject (computeItem r start) (computeItem r stop) substep

/-- `PyNumber_AsSsize_t(v, NULL)`: saturates instead of raising
(Objects/abstract.c, used by `_PyEval_SliceIndex`, Python/ceval.c:2949). -/
def clampSsize (x : Int) : Int := if x < ssizeMin then ssizeMin else if x > ssizeMax then ssizeMax else x

/-- `PySlice_Unpack`, sliceobject.c:218-262. -/
def sliceUnpack (s : Slice) : Py (Int × Int × Int) := do
  let step ← match s.step with
    | none => pure 1
    | some v =>
      let st := clampSsize v
      if st = 0 then throw (.valueError "slice step cannot be zero")
      pure (if st < -ssizeMax then -ssizeMax else st)
  let start := match s.start with
    | none => if step < 0 then ssizeMax else 0
    | some v => clampSsize v
  let stop := match s.stop with
    | none => if step < 0 then ssizeMin else ssizeMax
    | some v => clampSsize v
  return (start, stop, step)

/-- The start/stop adjustment block of `PySlice_AdjustIndices`,
sliceobject.c:273-291. `x += length` cannot overflow there because
`x < 0 ≤ length`. -/
def adjustOne (x length step : Int) : Int :=
  if x < 0 then
    let y := x + length
    if y < 0 then (if step < 0 then -1 else 0) else y
  else if x ≥ length then (if step < 0 then length - 1 else length)
  else x

/-- `PySlice_AdjustIndices`, sliceobject.c:264-304: `(start, stop, slicelength)`.
C division truncates (`Int.tdiv`). -/
def adjustIndices (length start stop step : Int) : Int × Int × Int :=
  let start := adjustOne start length step
  let stop := adjustOne stop length step
  let n :=
    if step < 0 then (if stop < start then Int.tdiv (start - stop - 1) (-step) + 1 else 0)
    else (if start < stop then Int.tdiv (stop - start - 1) step + 1 else 0)
  (start, stop, n)

/-- The positions `list[s]` reads for a list of length `n`:
`list_slice_subscript` and `list_slice_wrap`, Objects/listobject.c:3674-3703,
with `list_slice_lock_held` (:717-738) for `step == 1` and
`list_slice_step_lock_held` (:3654-3672) otherwise, whose cursor is a
`size_t` advanced by `(size_t)step`. -/
def listSlicePositions (n : Int) (s : Slice) : Py (List Int) := do
  let (start, stop, step) ← sliceUnpack s
  let (start, stop, len) := adjustIndices n start stop step
  if len ≤ 0 then return []
  else if step = 1 then
    return (List.range (stop - start).toNat).map (fun (i : Nat) => start + (i : Int))
  else
    return (List.range len.toNat).map (fun (i : Nat) => toU (toU start + (i : Int) * toU step))

/-! ## Membership, index, count, comparison, hash -/

/-- `range_contains_long`, rangeobject.c:458-501. -/
def rangeContainsLong (r : Range) (ob : Int) : Bool :=
  let (c2, c3) := if r.step > 0 then (decide (r.start ≤ ob), decide (ob < r.stop))
    else (decide (ob ≤ r.start), decide (r.stop < ob))
  if !c2 || !c3 then false
  else (ob - r.start) % r.step == 0

/-- `r.count(x)` for an int `x`, `range_count`, rangeobject.c:630-646. -/
def rangeCount (r : Range) (ob : Int) : Int := if rangeContainsLong r ob then 1 else 0

/-- `r.index(x)` for an int `x`, `range_index`, rangeobject.c:648-685. -/
def rangeIndex (r : Range) (ob : Int) : Py Int :=
  if rangeContainsLong r ob then
    let idx := ob - r.start
    if r.step = 1 then .ok idx else .ok (idx / r.step)
  else .error (.valueError "range.index(x): x not in range")

/-- `range_equals`, rangeobject.c:529-555, for two distinct objects. -/
def rangeEquals (r0 r1 : Range) : Bool :=
  if r0.length != r1.length then false
  else if r0.length == 0 then true
  else if r0.start != r1.start then false
  else if r0.length == 1 then true
  else r0.step == r1.step

/-- The tuple `range_hash` hashes, rangeobject.c:593-628:
`(len, None, None)`, `(len, start, None)` or `(len, start, step)`. -/
def rangeHashKey (r : Range) : Int × Option Int × Option Int :=
  if r.length == 0 then (r.length, none, none)
  else if r.length == 1 then (r.length, some r.start, none)
  else (r.length, some r.start, some r.step)

/-! ## Iterators -/

/-- `range_iterator` (`_PyRangeIterObject`, C longs, Include/internal/pycore_range.h)
and `longrange_iterator` (`longrangeiterobject`, PyLongs, rangeobject.c:12-17). -/
inductive RIter where
  | fast (start step len : Int)
  | long (start step len : Int)
  deriving Repr, DecidableEq, Inhabited

/-- `type(it).__name__`. -/
def RIter.typeName : RIter → String
  | .fast .. => "range_iterator"
  | .long .. => "longrange_iterator"

/-- `rangeiter_next` (rangeobject.c:845-859; same as `_ITER_NEXT_RANGE`,
Python/bytecodes.c:4082-4095) and `longrangeiter_next` (:1183-1191), which locks and
calls `longrangeiter_next_lock_held` (:1161-1181). `result + r->step` is signed
`long` arithmetic. -/
def iterNext : RIter → Option (Int × RIter)
  | .fast start step len =>
    if len > 0 then some (start, .fast (wrap (start + step)) step (len - 1)) else none
  | .long start step len =>
    if len > 0 then some (start, .long (start + step) step (len - 1)) else none

/-- The next `n` values (fewer if the iterator is exhausted) and the
iterator afterwards. -/
def iterTake : Nat → RIter → List Int × RIter
  | 0, it => ([], it)
  | n + 1, it =>
    match iterNext it with
    | none => ([], it)
    | some (x, it') => let (xs, it'') := iterTake n it'; (x :: xs, it'')

/-- `it.__length_hint__()`: `range_iterator___length_hint___impl`, rangeobject.c:869-874,
and `longrange_iterator___length_hint___impl`, :1044-1050. -/
def RIter.lengthHint : RIter → Int
  | .fast _ _ len | .long _ _ len => len

/-- The range inside `it.__reduce__()`: `range_iterator___reduce___impl`,
rangeobject.c:884-913 (`r->start + r->len * r->step` in signed `long`), and
`longrange_iterator___reduce___impl`, :1060-1087. -/
def iterReduce : RIter → Range
  | .fast start step len => makeRangeObject start (wrap (start + wrap (len * step))) step
  | .long start step len => makeRangeObject start (start + len * step) step

/-- `C long` conversion failure message (`PyLong_AsLong`). -/
def longOverflow : PyExc := .overflowError "Python int too large to convert to C long"

/-- `it.__setstate__(state)` for an exact int `state`:
`range_iterator___setstate___impl` (rangeobject.c:925-940, `PyLong_AsLong` then
clip) and `longrange_iterator___setstate___impl` (:1099-1142, clip in PyLong). -/
def iterSetstate (it : RIter) (state : Int) : Py RIter :=
  match it with
  | .fast start step len =>
    match asLong state with
    | none => .error longOverflow
    | some index =>
      let index := if index < 0 then 0 else if index > len then len else index
      .ok (.fast (wrap (start + wrap (index * step))) step (len - index))
  | .long start step len =>
    let st := if state < 0 then 0 else if len < state then len else state
    .ok (.long (start + st * step) step (len - st))

/-- The object passed to `it.__setstate__`. -/
inductive StateArg where
  /-- An object whose type is exactly `int`. -/
  | exact (v : Int)
  /-- An instance of a proper subclass `tp` of `int`, such as `bool`. -/
  | subclass (v : Int) (tp : String)
  /-- Not an `int`; its type `tp` defines `__index__`, which is a callback, with this
  outcome. An `__index__` that returns a non-int is a `TypeError` outcome. -/
  | index (r : Py Int) (tp : String)
  /-- Not an `int`, and its type `tp` has no `__index__`. -/
  | other (tp : String)
  deriving Inhabited

/-- `Py_TYPE(state)` as `%T` and `%.200s` print it. -/
def StateArg.typeName : StateArg → String
  | .exact _ => "int"
  | .subclass _ tp | .index _ tp | .other tp => tp

/-- `PyLong_AsLong(state)`, Objects/longobject.c:672-684, through
`PyLong_AsLongAndOverflow` (:593-667): an `int` of any subclass is read directly,
anything else goes through `_PyNumber_Index` (Objects/abstract.c:1410-1448). -/
def stateAsLong (s : StateArg) : Py Int :=
  let ofInt (v : Int) : Py Int := match asLong v with
    | some i => .ok i
    | none => .error longOverflow
  match s with
  | .exact v | .subclass v _ => ofInt v
  | .index r _ => r >>= ofInt
  | .other tp => .error (.typeError s!"'{tp}' object cannot be interpreted as an integer")

/-- `it.__setstate__(state)` for any object. The two iterators disagree on what they
accept: `range_iterator___setstate___impl` reads it with `PyLong_AsLong`
(rangeobject.c:929-931), so it takes `bool` and `__index__`, while
`longrange_iterator___setstate___impl` starts with `PyLong_CheckExact` (:1103-1106). -/
def iterSetstateObj (it : RIter) (state : StateArg) : Py RIter :=
  match it, state with
  | .fast .., _ => stateAsLong state >>= iterSetstate it
  | .long .., .exact v => iterSetstate it v
  | .long .., _ => .error (.typeError s!"state must be an int, not {state.typeName}")

/-- `iter(r)`: `range_iter`, rangeobject.c:1226-1279. -/
def rangeIter (r : Range) : RIter :=
  let slow := RIter.long r.start r.step r.length
  match asLong r.start, asLong r.stop, asLong r.step with
  | some lstart, some lstop, some lstep =>
    let ulen := getLenOfRange lstart lstop lstep
    if ulen > longMax then slow
    else if ulen ≠ 0 ∧ (if lstep > 0 then lstop > longMax - (lstep - 1)
                         else lstop < longMin + (-1 - lstep)) then slow
    else .fast lstart lstep ulen
  | _, _, _ => slow

/-- `reversed(r)`: `range_reverse`, rangeobject.c:1281-1383. The slow path
builds `longrange_iterator(start + (len - 1) * step, -step, len)`. -/
def rangeReverse (r : Range) : RIter :=
  let slow := RIter.long (r.start + (r.length - 1) * r.step) (-r.step) r.length
  match asLong r.start, asLong r.stop, asLong r.step with
  | some lstart, some lstop, some lstep =>
    if lstep = longMin then slow
    else if (if lstep > 0 then usub (toU lstart) (toU longMin) < toU lstep
             else usub (toU longMax) (toU lstart) < usub 0 (toU lstep)) then slow
    else
      let ulen := getLenOfRange lstart lstop lstep
      if ulen > longMax then slow
      else
        let newStop := wrap (lstart - lstep)
        let newStart := wrap (uadd (toU newStop) (umul ulen (toU lstep)))
        .fast newStart (wrap (-lstep)) ulen
  | _, _, _ => slow

/-! ## `PySlice_GetIndices` (C API) -/

/-- Return value, pending exception and output parameters of a C call. -/
structure CIndices where
  ret : Int
  exc : Option PyExc
  start : Int
  stop : Int
  step : Int
  deriving Repr, DecidableEq, Inhabited

/-- `PyLong_AsSsize_t` on an int: `-1` with `OverflowError` set on overflow. -/
def asSsizeC (v : Int) : Int × Option PyExc :=
  if ssizeMin ≤ v ∧ v ≤ ssizeMax then (v, none) else (-1, some ssizeOverflow)

/-- `PySlice_GetIndices(slice, length, &start, &stop, &step)`,
sliceobject.c:186-216, for int-or-None parts. A later exception replaces an
earlier one (`exc` is the one pending on return). -/
def sliceGetIndices (s : Slice) (length : Int) : CIndices :=
  let (step, e1) := match s.step with
    | none => ((1 : Int), (none : Option PyExc))
    | some v => asSsizeC v
  let (start, e2) := match s.start with
    | none => (if step < 0 then length - 1 else 0, (none : Option PyExc))
    | some v => let (x, e) := asSsizeC v; (if x < 0 then wrap (x + length) else x, e)
  let (stop, e3) := match s.stop with
    | none => (if step < 0 then -1 else length, (none : Option PyExc))
    | some v => let (x, e) := asSsizeC v; (if x < 0 then wrap (x + length) else x, e)
  let exc := e3 <|> e2 <|> e1
  let ret : Int := if stop > length then -1 else if start ≥ length then -1 else if step = 0 then -1 else 0
  ⟨ret, exc, start, stop, step⟩

end PyLean.RangeSlice
