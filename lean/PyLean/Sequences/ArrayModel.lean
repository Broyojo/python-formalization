import PyLean.Sequences.ListModel

/-!
Model of `array.array` (`Modules/arraymodule.c`, CPython 3.14.7) for the
integer typecodes `'b' 'B' 'h' 'i' 'q'` on LP64 (`short` 16, `int` 32,
`long`/`long long` 64 bits). An array is its typecode and its items; every
stored item fits the typecode (type invariant `Arr.WF`).
-/

namespace PyLean.Sequences

open PyLean
open PyLean.RangeSlice (Slice)

inductive TC where
  | b | B | h | i | q
  deriving Repr, DecidableEq, Inhabited

/-- The C value range of each typecode. -/
def TC.lo : TC → Int
  | .b => -128 | .B => 0 | .h => -32768 | .i => -2147483648 | .q => -9223372036854775808
def TC.hi : TC → Int
  | .b => 127 | .B => 255 | .h => 32767 | .i => 2147483647 | .q => 9223372036854775807
def TC.itemsize : TC → Int
  | .b => 1 | .B => 1 | .h => 2 | .i => 4 | .q => 8

structure Arr where
  tc : TC
  items : List Int
  deriving Repr, DecidableEq, Inhabited

/-- Type invariant: every item fits the typecode. -/
def Arr.WF (a : Arr) : Prop := ∀ x ∈ a.items, a.tc.lo ≤ x ∧ x ≤ a.tc.hi

def longOverflow : PyExc := .overflowError "Python int too large to convert to C long"

/-- `PyLong_AsLong` (Objects/longobject.c:601). -/
def asLong (v : Int) : Py Int :=
  if -9223372036854775808 ≤ v ∧ v ≤ 9223372036854775807 then .ok v else .error longOverflow

/-- The conversion half of each `*_setitem` (`PyArg_Parse` with the format
the setitem uses, Python/getargs.c:682-829, then the setitem's own range
check), arraymodule.c:243-268 (`b`), :277-290 (`B`), :372-384 (`h`),
:425-437 (`i`), :551-563 (`q`). Returns the C value. The bounds check
`CHECK_ARRAY_BOUNDS` sits between parsing and the `b` range check; callers
pass `idxOk` (always true for `i = -1` and for in-range indices). -/
def tcSetitem (tc : TC) (idxOk : Bool) (v : Int) : Py Int := do
  let boundsErr : PyExc := .indexError "array assignment index out of range"
  match tc with
  | .b =>
    -- PyArg_Parse(v, "h;...")
    let x ← asLong v
    if x < -32768 then throw (.overflowError "signed short integer is less than minimum")
    if x > 32767 then throw (.overflowError "signed short integer is greater than maximum")
    if !idxOk then throw boundsErr
    if x < -128 then throw (.overflowError "signed char is less than minimum")
    if x > 127 then throw (.overflowError "signed char is greater than maximum")
    return x
  | .B =>
    -- PyArg_Parse(v, "b;...")
    let x ← asLong v
    if x < 0 then throw (.overflowError "unsigned byte integer is less than minimum")
    if x > 255 then throw (.overflowError "unsigned byte integer is greater than maximum")
    if !idxOk then throw boundsErr
    return x
  | .h =>
    let x ← asLong v
    if x < -32768 then throw (.overflowError "signed short integer is less than minimum")
    if x > 32767 then throw (.overflowError "signed short integer is greater than maximum")
    if !idxOk then throw boundsErr
    return x
  | .i =>
    let x ← asLong v
    if x > 2147483647 then throw (.overflowError "signed integer is greater than maximum")
    if x < -2147483648 then throw (.overflowError "signed integer is less than minimum")
    if !idxOk then throw boundsErr
    return x
  | .q =>
    -- PyArg_Parse(v, "L;..."): PyLong_AsLongLong, Objects/longobject.c:1172
    if ¬ (-9223372036854775808 ≤ v ∧ v ≤ 9223372036854775807) then
      throw (.overflowError "int too big to convert")
    if !idxOk then throw boundsErr
    return v

/-- `ins1` (arraymodule.c:761-789): check the value with `setitem(self, -1, v)`,
grow, clip `where` like `list.insert`, store. -/
def arrIns1 (a : Arr) (where_ v : Int) : Py Arr := do
  let x ← tcSetitem a.tc true v
  return { a with items := insAt a.items (ins1Pos a.items.length where_).toNat x }

/-- `a.append(v)`: `ins(self, Py_SIZE(self), v)` (arraymodule.c:1502-1506). -/
def arrAppend (a : Arr) (v : Int) : Py Arr := arrIns1 a a.items.length v

/-- `a.insert(i, v)` (arraymodule.c:1449-1463). -/
def arrInsert (a : Arr) (i v : Int) : Py Arr := do
  let i ← asSsize i
  arrIns1 a i v

/-- `array(tc, items)` for a list initializer (`array_new`,
arraymodule.c:2882-2898): every item through `setarrayitem`; any failure
discards the new array. -/
def arrNew (tc : TC) (items : List Int) : Py Arr := do
  let xs ← items.mapM (tcSetitem tc true)
  return ⟨tc, xs⟩

/-- `a.extend(iterable)` for a non-array iterable: `array_iter_extend`
(arraymodule.c:1139-1160) appends item by item, so a failing item leaves the
earlier ones appended. Returns the array reached and the error, if any. -/
def arrIterExtend (a : Arr) : List Int → Arr × Option PyExc
  | [] => (a, none)
  | v :: vs =>
    match arrIns1 a a.items.length v with
    | .ok a' => arrIterExtend a' vs
    | .error e => (a, some e)

/-- `a.pop([i])` (arraymodule.c:1391-1415). -/
def arrPopK (a : Arr) (i : Int) : Py (Int × Arr) := do
  let n : Int := a.items.length
  if n = 0 then throw (.indexError "pop from empty array")
  let i := if i < 0 then i + n else i
  if i < 0 ∨ i ≥ n then throw (.indexError "pop index out of range")
  return (ix a.items i, { a with items := a.items.eraseIdx i.toNat })

def arrPop (a : Arr) (i : Option Int) : Py (Int × Arr) := popArg i >>= arrPopK a

/-- The loop of `array_array_index_impl` (arraymodule.c:3307-3321):
`for (i = start; i < stop && i < Py_SIZE(self); i++)`. -/
def arrIndexLoop (l : List Int) (x stop : Int) : Int → Nat → Option Int
  | _, 0 => none
  | i, fuel + 1 =>
    if i < stop ∧ i < l.length then
      (if ix l i = x then some i else arrIndexLoop l x stop (i + 1) fuel)
    else none

/-- `a.index(x[, start[, stop]])` (arraymodule.c:1293-1326). Unlike
`list.index`, a negative `stop` is not clipped at 0 (harmless: the loop
condition then fails at once). -/
def arrIndex (a : Arr) (x : Int) (start stop : Option Int) : Py Int :=
  let n : Int := a.items.length
  let start := sliceIndex (start.getD 0)
  let stop := sliceIndex (stop.getD ssizeMax)
  let start := if start < 0 then (if start + n < 0 then 0 else start + n) else start
  let stop := if stop < 0 then stop + n else stop
  match arrIndexLoop a.items x stop start (a.items.length + 1) with
  | some i => .ok i
  | none => .error (.valueError "array.index(x): x not in array")

/-- `a.count(x)` (arraymodule.c:1255-1275). -/
def arrCount (a : Arr) (x : Int) : Int := (a.items.filter (· == x)).length

/-- `a.remove(x)` (arraymodule.c:1353-1378), deleting with
`array_del_slice(self, i, i+1)`. -/
def arrRemove (a : Arr) (x : Int) : Py Arr :=
  match firstFrom a.items x 0 a.items.length with
  | some i => .ok { a with items := a.items.eraseIdx i }
  | none => .error (.valueError "array.remove(x): x not in array")

/-- `a[i]` (`array_subscr`, arraymodule.c:2527-2535, and `array_item`, :931-939). -/
def arrGetItem (a : Arr) (i : Int) : Py Int := do
  let i ← subIndex i
  let i := if i < 0 then i + a.items.length else i
  if i < 0 ∨ i ≥ a.items.length then throw (.indexError "array index out of range")
  return ix a.items i

/-- `array_del_slice(a, ilow, ihigh)` (arraymodule.c:1080-1113). -/
def arrDelSlice (l : List Int) (ilow ihigh : Int) : List Int :=
  let n : Int := l.length
  let ilow := if ilow < 0 then 0 else if ilow > n then n else ilow
  let ihigh := if ihigh < 0 then 0 else ihigh
  let ihigh := if ihigh < ilow then ilow else if ihigh > n then n else ihigh
  l.take ilow.toNat ++ l.drop ihigh.toNat

/-- `a[s] = value` / `del a[s]`: `array_ass_subscr` (arraymodule.c:2587-2742).
`key` is an int index or a slice; `value` is `none` (delete) or the items of
an array of the same typecode. -/
def arrAssSubscr (a : Arr) (key : Int ⊕ Slice) (value : Option (List Int)) : Py Arr := do
  let size : Int := a.items.length
  -- (start, stop, step, slicelength), or a direct store
  let (start, stop, step, len) ← match key with
    | .inl i => do
      let i ← subIndex i
      let i := if i < 0 then i + size else i
      if i < 0 ∨ i ≥ size then throw (.indexError "array assignment index out of range")
      match value with
      | none => pure (i, i + 1, (1 : Int), (1 : Int))
      | some _ => pure (i, i, 0, 0)
    | .inr s => do
      let (start, stop, step) ← RangeSlice.sliceUnpack s
      let (start, stop, len) := RangeSlice.adjustIndices size start stop step
      pure (start, stop, step, len)
  -- int store: `(*self->ob_descr->setitem)(self, i, value)`
  if step = 0 then
    match value with
    | some [v] => do
      let x ← tcSetitem a.tc true v
      return { a with items := a.items.set start.toNat x }
    | _ => throw (cUB "int store without a single value")
  let needed : Int := match value with | none => 0 | some vs => vs.length
  let stop := if (step > 0 ∧ stop < start) ∨ (step < 0 ∧ stop > start) then start else stop
  if step = 1 then
    -- the two memmove/resize branches and the memcpy, :2671-2692
    return { a with items := a.items.take start.toNat ++ value.getD [] ++ a.items.drop stop.toNat }
  else if needed = 0 then
    -- "Delete slice", :2695-2723 (also taken for `a[::k] = array()`)
    if len ≤ 0 then
      -- the loops do nothing and `array_resize` keeps the size
      return a
    let items ← delExtended a.items start stop step len
    return { a with items := items }
  else
    if needed ≠ len then
      throw (.valueError s!"attempt to assign array of size {needed} to extended slice of size {len}")
    return { a with items := storeLoop a.items start step (value.getD []) }

/-- `a *= n` (`array_inplace_repeat`, arraymodule.c:1212-1236). -/
def arrIRepeat (a : Arr) (n : Int) : Py Arr := do
  let n ← repeatCount n
  let size : Int := a.items.length
  if size > 0 ∧ n ≠ 1 then
    let n := if n < 0 then 0 else n
    if size > ssizeMax / a.tc.itemsize then throw memoryError
    let bytes := size * a.tc.itemsize
    if n > 0 ∧ bytes > ssizeMax / n then throw memoryError
    return { a with items := (List.replicate n.toNat a.items).flatten }
  return a

/-- `a * n` (`array_repeat`, arraymodule.c:1051-1078, with
`newarrayobject_untracked`'s overflow check, :706-709). -/
def arrRepeat (a : Arr) (n : Int) : Py Arr := do
  let n ← repeatCount n
  let n := if n < 0 then 0 else n
  let len : Int := a.items.length
  if len ≠ 0 ∧ n > ssizeMax / len then throw memoryError
  let size := len * n
  if size > ssizeMax / a.tc.itemsize then throw memoryError
  if size = 0 then return { a with items := [] }
  return { a with items := (List.replicate n.toNat a.items).flatten }

end PyLean.Sequences
