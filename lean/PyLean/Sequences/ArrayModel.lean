import PyLean.Sequences.ListModel
import PyLean.Sequences.Values

/-!
Model of `array.array` (`Modules/arraymodule.c`, CPython 3.14.7), all fourteen
typecodes, LP64 (see `Values.lean`).

An array keeps the fields of `arrayobject` that have a visible effect: the
descriptor (`tc`), the items, `allocated`, whether `ob_item` is NULL, and
`ob_exports`, plus the type's name (`"array"` or a subclass that does not override
`__new__`). `items` holds the C value of each element: the signed or unsigned
integer, the `wchar_t` (signed) or `Py_UCS4` for `u`/`w`, and the IEEE bit pattern
for `f`/`d`. Reading the buffer as bytes is `itemBytes`. Items past the size
that `array_resize` exposes are 0 in the model; every caller overwrites them
before they can be read.

The element comparison `PyObject_RichCompareBool(item, v, Py_EQ)` of `count`,
`index`, `remove` and `in` is a parameter `eqv : PyVal → Py Bool` (the object `v`
is closed over, and may raise). A `v` that mutates the array during comparison
is out of scope; `pvEq` is the comparison for ints, floats and strs.
-/

namespace PyLean.Sequences

open PyLean
open PyLean.RangeSlice (Slice sliceUnpack adjustIndices toU wrap)

inductive TC where
  | b | B | u | w | h | H | i | I | l | L | q | Q | f | d
  deriving Repr, DecidableEq, Inhabited

/-- The `descriptors` table, in order (arraymodule.c:673-690). -/
def TC.all : List TC := [.b, .B, .u, .w, .h, .H, .i, .I, .l, .L, .q, .Q, .f, .d]

/-- `descr->typecode`. -/
def TC.code : TC → Char
  | .b => 'b' | .B => 'B' | .u => 'u' | .w => 'w' | .h => 'h' | .H => 'H' | .i => 'i'
  | .I => 'I' | .l => 'l' | .L => 'L' | .q => 'q' | .Q => 'Q' | .f => 'f' | .d => 'd'

/-- `descr->itemsize`. -/
def TC.itemsize : TC → Int
  | .b | .B => 1
  | .h | .H => 2
  | .u | .w | .i | .I | .f => 4
  | .l | .L | .q | .Q | .d => 8

/-- `descr->is_integer_type`. -/
def TC.isInteger : TC → Bool
  | .u | .w | .f | .d => false
  | _ => true

/-- `descr->is_signed`. -/
def TC.isSigned : TC → Bool
  | .b | .h | .i | .l | .q => true
  | _ => false

/-- `descr->compareitems != NULL`. -/
def TC.hasCompare : TC → Bool
  | .f | .d => false
  | _ => true

/-- `descr->formats`, as `array_buffer_getbuf` exports it (`u` is `w`, :2774-2780). -/
def TC.format : TC → String
  | .u => "w"
  | t => t.code.toString

/-- The range of the C element. -/
def TC.lo : TC → Int
  | .b => -128 | .h => -32768 | .i | .u => -2147483648 | .l | .q => -9223372036854775808
  | _ => 0
def TC.hi : TC → Int
  | .b => 127 | .B => 255 | .h => 32767 | .H => 65535 | .i | .u => 2147483647
  | .I | .w | .f => 4294967295
  | .l | .q => 9223372036854775807
  | .L | .Q | .d => 18446744073709551615

structure Arr where
  tc : TC
  items : List Int
  allocated : Int
  hasBuf : Bool
  exports : Nat
  tname : String
  deriving Repr, DecidableEq

instance : Inhabited Arr := ⟨⟨.b, [], 0, false, 0, "array"⟩⟩

/-- Type invariant: every item fits the C element type. -/
def Arr.WF (a : Arr) : Prop := ∀ x ∈ a.items, a.tc.lo ≤ x ∧ x ≤ a.tc.hi

def bufferErr : PyExc := .named "BufferError" "cannot resize an array that is exporting buffers"

/-- `size` items: truncate, or expose new slots holding 0. -/
def resized (l : List Int) (n : Int) : List Int :=
  if n ≤ l.length then l.take n.toNat else l ++ List.replicate (n - l.length).toNat 0

/-- `array_resize` (arraymodule.c:135-192). -/
def arrResize (a : Arr) (newsize : Int) : Py Arr :=
  let size : Int := a.items.length
  if a.exports > 0 ∧ newsize ≠ size then .error bufferErr
  else if a.allocated ≥ newsize ∧ size < newsize + 16 ∧ a.hasBuf then
    .ok { a with items := resized a.items newsize }
  else if newsize = 0 then .ok { a with items := [], hasBuf := false, allocated := 0 }
  else
    let newAlloc := newsize / 16 + (if size < 8 then 3 else 7) + newsize
    if newAlloc ≤ 18446744073709551615 / a.tc.itemsize then
      .ok { a with items := resized a.items newsize, hasBuf := true, allocated := newAlloc }
    else .error memoryError

/-! ### Items -/

/-- The `*_getitem` functions (arraymodule.c:236-241, 270-275, 292-296, 335-339,
365-370, 387-391, 419-423, 440-445, 487-491, 507-511, 545-549, 565-570, 604-608,
624-628). The character types go through `PyUnicode_FromOrdinal`, whose argument
is a C `int` (Objects/unicodeobject.c:3518-3527). -/
def tcGetitem (tc : TC) (x : Int) : Py PyVal :=
  match tc with
  | .u | .w =>
    if x < 0 ∨ x > 1114111 then .error (.valueError "chr() arg not in range(0x110000)")
    else .ok (.str [x.toNat])
  | .f => .ok (.float (floatToDouble x.toNat))
  | .d => .ok (.float x.toNat)
  | _ => .ok (.int x)

/-- The conversion of `b_setitem` (arraymodule.c:243-268), ... `d_setitem`
(:630-642): `PyArg_Parse` with the setitem's format (Python/getargs.c:682-829),
`CHECK_ARRAY_BOUNDS`, the setitem's own range check. Returns the C value. `idxOk`
is the bounds check's outcome, true except when `__index__` shrinks the array. -/
def tcSetitem (tc : TC) (idxOk : Bool) (v : PyVal) : Py Int := do
  let boundsErr : PyExc := .indexError "array assignment index out of range"
  match tc with
  | .b =>
    -- PyArg_Parse(v, "h;...")
    let x ← asLongV v
    if x < -32768 then throw (.overflowError "signed short integer is less than minimum")
    if x > 32767 then throw (.overflowError "signed short integer is greater than maximum")
    if !idxOk then throw boundsErr
    if x < -128 then throw (.overflowError "signed char is less than minimum")
    if x > 127 then throw (.overflowError "signed char is greater than maximum")
    return x
  | .B =>
    -- PyArg_Parse(v, "b;...")
    let x ← asLongV v
    if x < 0 then throw (.overflowError "unsigned byte integer is less than minimum")
    if x > 255 then throw (.overflowError "unsigned byte integer is greater than maximum")
    if !idxOk then throw boundsErr
    return x
  | .h =>
    let x ← asLongV v
    if x < -32768 then throw (.overflowError "signed short integer is less than minimum")
    if x > 32767 then throw (.overflowError "signed short integer is greater than maximum")
    if !idxOk then throw boundsErr
    return x
  | .H =>
    -- PyArg_Parse(v, "i;...")
    let x ← asLongV v
    if x > 2147483647 then throw (.overflowError "signed integer is greater than maximum")
    if x < -2147483648 then throw (.overflowError "signed integer is less than minimum")
    if x < 0 then throw (.overflowError "unsigned short is less than minimum")
    if x > 65535 then throw (.overflowError "unsigned short is greater than maximum")
    if !idxOk then throw boundsErr
    return x
  | .i =>
    let x ← asLongV v
    if x > 2147483647 then throw (.overflowError "signed integer is greater than maximum")
    if x < -2147483648 then throw (.overflowError "signed integer is less than minimum")
    if !idxOk then throw boundsErr
    return x
  | .I =>
    -- _PyNumber_Index, PyLong_AsUnsignedLong (Objects/longobject.c:677-727)
    let x ← toIndex v
    if x < 0 then throw (.overflowError "can't convert negative value to unsigned int")
    if x > 18446744073709551615 then
      throw (.overflowError "Python int too large to convert to C unsigned long")
    if x > 4294967295 then throw (.overflowError "unsigned int is greater than maximum")
    if !idxOk then throw boundsErr
    return x
  | .l =>
    let x ← asLongV v
    if !idxOk then throw boundsErr
    return x
  | .L =>
    let x ← toIndex v
    if x < 0 then throw (.overflowError "can't convert negative value to unsigned int")
    if x > 18446744073709551615 then
      throw (.overflowError "Python int too large to convert to C unsigned long")
    if !idxOk then throw boundsErr
    return x
  | .q =>
    -- PyArg_Parse(v, "L;..."): PyLong_AsLongLong through _PyLong_AsByteArray
    -- (Objects/longobject.c:1031-1172)
    let x ← toIndex v
    if ¬ (longMin ≤ x ∧ x ≤ longMax) then throw (.overflowError "int too big to convert")
    if !idxOk then throw boundsErr
    return x
  | .Q =>
    let x ← toIndex v
    if x < 0 then throw (.overflowError "can't convert negative int to unsigned")
    if x > 18446744073709551615 then throw (.overflowError "int too big to convert")
    if !idxOk then throw boundsErr
    return x
  | .u | .w =>
    -- u_setitem (:298-333), w_setitem (:341-363); wchar_t holds any code point here
    match v with
    | .str [c] =>
      if !idxOk then throw boundsErr
      return (c : Int)
    | .str cs =>
      throw (.typeError s!"array item must be a unicode character, not a string of length {cs.length}")
    | v => throw (.typeError s!"array item must be a unicode character, not {v.typeName}")
  | .f =>
    -- PyArg_Parse(v, "f;..."): (float)PyFloat_AsDouble(v), Python/getargs.c
    let x ← asDouble v
    if !idxOk then throw boundsErr
    return (doubleToFloat x : Int)
  | .d =>
    let x ← asDouble v
    if !idxOk then throw boundsErr
    return (x : Int)

/-- `getarrayitem` (arraymodule.c:748-759). `array_item` (:931-939) adds the range
check. -/
def Arr.get (a : Arr) (i : Int) : Py PyVal := tcGetitem a.tc (ix a.items i)

/-- `len(a)` (`array_length`, arraymodule.c:926-929). -/
def arrLength (a : Arr) : Int := a.items.length

/-- `array_item` (arraymodule.c:931-939), the `sq_item` slot: `PySequence_GetItem`
has added `len` to a negative index. -/
def arrItem (a : Arr) (i : Int) : Py PyVal :=
  if i < 0 ∨ i ≥ a.items.length then .error (.indexError "array index out of range")
  else a.get i

/-- `memcpy(items + start, src, len(src))`. -/
def memcpy (l : List Int) (start : Int) (src : List Int) : List Int :=
  l.take start.toNat ++ src ++ l.drop (start + src.length).toNat

/-- `newarrayobject_untracked` (arraymodule.c:699-736), with `newarrayobject`
(:738-746): `size` zeroed items of descriptor `tc`, `allocated == size`, `ob_item`
NULL for size 0. -/
def newArr (tname : String) (tc : TC) (size : Int) : Py Arr :=
  if size > ssizeMax / tc.itemsize then .error memoryError
  else .ok ⟨tc, List.replicate size.toNat 0, size, decide (size > 0), 0, tname⟩

/-- `array_slice` (arraymodule.c:942-967): a new `array.array` (never a subclass). -/
def arrSlice (a : Arr) (ilow ihigh : Int) : Py Arr := do
  let n : Int := a.items.length
  let ilow := if ilow < 0 then 0 else if ilow > n then n else ilow
  let ihigh := if ihigh < 0 then 0 else ihigh
  let ihigh := if ihigh < ilow then ilow else if ihigh > n then n else ihigh
  let np ← newArr "array" a.tc (ihigh - ilow)
  if ihigh > ilow then
    return { np with items := (a.items.drop ilow.toNat).take (ihigh - ilow).toNat }
  else return np

/-- `a.clear()` (`array_array_clear_impl`, arraymodule.c:975-982). -/
def arrClear (a : Arr) : Py Arr := arrResize a 0

/-- `a.__copy__()`, `a.__deepcopy__(memo)` (arraymodule.c:991-1010). -/
def arrCopy (a : Arr) : Py Arr := arrSlice a 0 a.items.length

/-- `ins1` (arraymodule.c:761-789): check the value with `setitem(self, -1, v)`,
grow, clip `where` like `list.insert`, shift, store. -/
def arrIns1 (a : Arr) (where_ : Int) (v : PyVal) : Py Arr := do
  let n : Int := a.items.length
  let _ ← tcSetitem a.tc true v
  let a ← arrResize a (n + 1)
  let w := ins1Pos n where_
  let items ← if w ≠ n then memmove a.items (w + 1) w (n - w) else pure a.items
  let x ← tcSetitem a.tc true v
  return { a with items := items.set w.toNat x }

/-- `a.append(v)` (`ins(self, Py_SIZE(self), v)`, arraymodule.c:1502-1506). -/
def arrAppend (a : Arr) (v : PyVal) : Py Arr := arrIns1 a a.items.length v

/-- `a.insert(i, v)` (`ins`, :1239-1245, `array_array_insert_impl`, :1450-1454). -/
def arrInsert (a : Arr) (i : Int) (v : PyVal) : Py Arr := do
  let i ← asSsize i
  arrIns1 a i v

/-- `array_del_slice` (arraymodule.c:1081-1113). -/
def arrDelSlice (a : Arr) (ilow ihigh : Int) : Py Arr := do
  let size : Int := a.items.length
  let ilow := if ilow < 0 then 0 else if ilow > size then size else ilow
  let ihigh := if ihigh < 0 then 0 else ihigh
  let ihigh := if ihigh < ilow then ilow else if ihigh > size then size else ihigh
  let d := ihigh - ilow
  if d ≠ 0 ∧ a.exports > 0 then throw bufferErr
  if d > 0 then
    let items ← memmove a.items (ihigh - d) ihigh (size - ihigh)
    arrResize { a with items } (size - d)
  else return a

/-- `array_ass_item` (arraymodule.c:1116-1127), the `sq_ass_item` slot, and
`setarrayitem` (:1130-1137). -/
def arrAssItem (a : Arr) (i : Int) (v : Option PyVal) : Py Arr := do
  if i < 0 ∨ i ≥ a.items.length then throw (.indexError "array assignment index out of range")
  match v with
  | none => arrDelSlice a i (i + 1)
  | some v =>
    let x ← tcSetitem a.tc true v
    return { a with items := a.items.set i.toNat x }

/-- `array(c, initial)` from the arguments of `PyArg_ParseTuple("C|O:array")`
(Python/getargs.c `C` format): the typecode must be a string of length 1. -/
def arrCtorCheck (typecode : PyVal) : Py Char :=
  match typecode with
  | .str [c] => .ok (Char.ofNat c)
  | .str cs => .error (.typeError
      s!"array() argument 1 must be a unicode character, not a string of length {cs.length}")
  | v =>
    let t := if v == .obj "NoneType" none then "None" else v.typeName
    .error (.typeError s!"array() argument 1 must be a unicode character, not {t}")

/-- `array_iter_extend` (arraymodule.c:1140-1160): `ins1` per item, so a failing
item leaves the earlier ones appended. The array reached, and the error. -/
def arrIterItems (a : Arr) : List PyVal → Arr × Option PyExc
  | [] => (a, none)
  | v :: vs =>
    match arrIns1 a a.items.length v with
    | .ok a' => arrIterItems a' vs
    | .error e => (a, some e)

def arrIterExtend (a : Arr) (src : PyIterable PyVal) : Arr × Option PyExc :=
  match src with
  | .notIterable t => (a, some (notIterableErr t))
  | .iter xs e =>
    match arrIterItems a xs with
    | (a, some err) => (a, some err)
    | (a, none) =>
      match e with
      | some .stopIteration => (a, none)
      | e => (a, e)

/-- `array_do_extend` for an array `b` (arraymodule.c:1163-1193); `same` says `b is a`. -/
def arrDoExtendArr (a b : Arr) : Py Arr := do
  if a.tc ≠ b.tc then throw (.typeError "can only extend with array of same kind")
  let sa : Int := a.items.length
  let sb : Int := b.items.length
  if sa > ssizeMax - sb ∨ sa + sb > ssizeMax / a.tc.itemsize then throw memoryError
  let a' ← arrResize a (sa + sb)
  if sb > 0 then return { a' with items := memcpy a'.items sa b.items }
  else return a'

/-- `a.extend(x)` (`array_array_extend_impl`, arraymodule.c:1429-1436). -/
def arrExtend (a : Arr) (x : Arr ⊕ PyIterable PyVal) : Arr × Option PyExc :=
  match x with
  | .inl b =>
    match arrDoExtendArr a b with
    | .ok a' => (a', none)
    | .error e => (a, some e)
  | .inr src => arrIterExtend a src

/-- `a + b` (`array_concat`, arraymodule.c:1014-1049). -/
def arrConcat (a : Arr) (bb : Arr ⊕ String) : Py Arr := do
  match bb with
  | .inr t => throw (.typeError s!"can only append array (not \"{t}\") to array")
  | .inl b =>
    if a.tc ≠ b.tc then throw (.typeError "bad argument type for built-in operation")
    let sa : Int := a.items.length
    let sb : Int := b.items.length
    if sa > ssizeMax - sb then throw memoryError
    let np ← newArr "array" a.tc (sa + sb)
    return { np with items := a.items ++ b.items }

/-- `a += b` (`array_inplace_concat`, arraymodule.c:1196-1210). -/
def arrIConcat (a : Arr) (bb : Arr ⊕ String) : Py Arr :=
  match bb with
  | .inr t => .error (.typeError s!"can only extend array with array (not \"{t}\")")
  | .inl b => arrDoExtendArr a b

/-- `a * n` (`array_repeat`, arraymodule.c:1052-1078) for a `Py_ssize_t` `n`. -/
def arrRepeatC (a : Arr) (n : Int) : Py Arr := do
  let n := if n < 0 then 0 else n
  let len : Int := a.items.length
  if len ≠ 0 ∧ n > ssizeMax / len then throw memoryError
  let size := len * n
  let np ← newArr "array" a.tc size
  if size = 0 then return np
  return { np with items := (List.replicate n.toNat a.items).flatten }

def arrRepeat (a : Arr) (n : Int) : Py Arr := do
  let n ← repeatCount n
  arrRepeatC a n

/-- `a *= n` (`array_inplace_repeat`, arraymodule.c:1213-1236). -/
def arrIRepeatC (a : Arr) (n : Int) : Py Arr := do
  let size : Int := a.items.length
  if size > 0 ∧ n ≠ 1 then
    let n := if n < 0 then 0 else n
    if size > ssizeMax / a.tc.itemsize then throw memoryError
    let bytes := size * a.tc.itemsize
    if n > 0 ∧ bytes > ssizeMax / n then throw memoryError
    let items := a.items
    let a ← arrResize a (n * size)
    return { a with items := (List.replicate n.toNat items).flatten }
  return a

def arrIRepeat (a : Arr) (n : Int) : Py Arr := do
  let n ← repeatCount n
  arrIRepeatC a n

/-! ### Searching -/

/-- `a.count(v)` (`array_array_count_impl`, arraymodule.c:1256-1275). -/
def arrCountLoop (a : Arr) (eqv : PyVal → Py Bool) : Nat → Int → Int → Py Int
  | 0, _, c => .ok c
  | n + 1, i, c =>
    match a.get i with
    | .error e => .error e
    | .ok x =>
      match eqv x with
      | .error e => .error e
      | .ok b => arrCountLoop a eqv n (i + 1) (if b then c + 1 else c)

def arrCount (a : Arr) (eqv : PyVal → Py Bool) : Py Int := arrCountLoop a eqv a.items.length 0 0

/-- The scan of `array_array_index_impl` (arraymodule.c:1307-1321):
`for (i = start; i < stop && i < Py_SIZE(self); i++)`; of
`array_array_remove_impl` (:1358-1375) with `stop == size`; of `array_contains`
(:1333-1339). `.ok (some i)` is the first match. -/
def arrScan (a : Arr) (eqv : PyVal → Py Bool) (stop : Int) : Nat → Int → Py (Option Int)
  | 0, _ => .ok none
  | fuel + 1, i =>
    if i < stop ∧ i < a.items.length then
      match a.get i with
      | .error e => .error e
      | .ok x =>
        match eqv x with
        | .error e => .error e
        | .ok true => .ok (some i)
        | .ok false => arrScan a eqv stop fuel (i + 1)
    else .ok none

/-- `a.index(v[, start[, stop]])` (arraymodule.c:1294-1326). Unlike
`list.index`, a negative `stop` is not clipped at 0 (harmless: the loop
condition then fails at once). -/
def arrIndex (a : Arr) (eqv : PyVal → Py Bool) (start stop : Option Int) : Py Int :=
  let n : Int := a.items.length
  let start := sliceIndex (start.getD 0)
  let stop := sliceIndex (stop.getD ssizeMax)
  let start := if start < 0 then (if start + n < 0 then 0 else start + n) else start
  let stop := if stop < 0 then stop + n else stop
  match arrScan a eqv stop (a.items.length + 1) start with
  | .error e => .error e
  | .ok (some i) => .ok i
  | .ok none => .error (.valueError "array.index(x): x not in array")

/-- `v in a` (`array_contains`, arraymodule.c:1329-1341). -/
def arrContains (a : Arr) (eqv : PyVal → Py Bool) : Py Bool :=
  match arrScan a eqv a.items.length (a.items.length + 1) 0 with
  | .error e => .error e
  | .ok r => .ok r.isSome

/-- `a.remove(v)` (`array_array_remove_impl`, arraymodule.c:1354-1378), deleting
with `array_del_slice(self, i, i+1)`. -/
def arrRemove (a : Arr) (eqv : PyVal → Py Bool) : Py Arr :=
  match arrScan a eqv a.items.length (a.items.length + 1) 0 with
  | .error e => .error e
  | .ok (some i) => arrDelSlice a i (i + 1)
  | .ok none => .error (.valueError "array.remove(x): x not in array")

/-- The body of `array_array_pop_impl` (arraymodule.c:1392-1415). -/
def arrPopK (a : Arr) (i : Int) : Py (PyVal × Arr) := do
  let n : Int := a.items.length
  if n = 0 then throw (.indexError "pop from empty array")
  let i := if i < 0 then i + n else i
  if i < 0 ∨ i ≥ n then throw (.indexError "pop index out of range")
  let v ← a.get i
  let a ← arrDelSlice a i (i + 1)
  return (v, a)

/-- `a.pop([i])`: Argument Clinic `Py_ssize_t` (default -1). -/
def arrPop (a : Arr) (i : Option Int) : Py (PyVal × Arr) := popArg i >>= arrPopK a

/-! ### Subscripts -/

/-- `a[i]` for an int `i` (`array_subscr`, arraymodule.c:2528-2535). -/
def arrGetItem (a : Arr) (i : Int) : Py PyVal := do
  let i ← subIndex i
  let i := if i < 0 then i + a.items.length else i
  arrItem a i

/-- `a[s]` for a slice (`array_subscr`, arraymodule.c:2537-2577): a new `array.array`. -/
def arrGetSlice (a : Arr) (s : Slice) : Py Arr := do
  let (start, stop, step) ← sliceUnpack s
  let (start, _, len) := adjustIndices a.items.length start stop step
  if len ≤ 0 then return (← newArr "array" a.tc 0)
  let np ← newArr "array" a.tc len
  if step = 1 then
    return { np with items := (a.items.drop start.toNat).take len.toNat }
  return { np with items := ((List.range len.toNat).map
    (fun (i : Nat) => ix a.items (toU (toU start + (i : Int) * toU step)))) }

/-- The right-hand side of `a[s] = value`. -/
inductive SliceVal where
  /-- `del a[s]`. -/
  | delete
  /-- An array; `same` says it is `a` itself. -/
  | arr (other : Arr) (same : Bool)
  /-- Anything else, of this type. -/
  | other (tname : String)

/-- The compaction loop of the extended-slice deletion in `array_ass_subscr`
(arraymodule.c:2705-2716): `for (cur = start, i = 0; i < slicelength; cur += step, i++)`,
moving the `lim` items after each deleted one down by `i + 1`. -/
def arrDelLoop (size step len : Int) : Nat → List Int → Int → Int → Py (List Int)
  | 0, mem, _, _ => .ok mem
  | fuel + 1, mem, cur, i =>
    if i < len then
      let lim := if cur + step ≥ size then size - cur - 1 else step - 1
      match memmove mem (cur - i) (cur + 1) lim with
      | .ok mem => arrDelLoop size step len fuel mem (cur + step) (i + 1)
      | .error e => .error e
    else .ok mem

/-- The part of `array_ass_subscr` after the key is decoded
(arraymodule.c:2626-2742); `other` is `none` for `value == NULL`. -/
def arrAssCore (a : Arr) (start stop step len : Int) (other : Option (List Int)) : Py Arr := do
  let size : Int := a.items.length
  let needed : Int := match other with | none => 0 | some o => o.length
  let src := other.getD []
  let stop := if (step > 0 ∧ stop < start) ∨ (step < 0 ∧ stop > start) then start else stop
  if (needed = 0 ∨ len ≠ needed) ∧ a.exports > 0 then throw bufferErr
  if step = 1 then
    let a ←
      if len > needed then do
        let items ← memmove a.items (start + needed) stop (size - stop)
        arrResize { a with items } (size + needed - len)
      else if len < needed then do
        let a ← arrResize a (size + needed - len)
        let items ← memmove a.items (start + needed) stop (size + needed - len - start - needed)
        pure { a with items }
      else pure a
    if needed > 0 then return { a with items := memcpy a.items start src }
    return a
  else if needed = 0 then
    -- "Delete slice", :2695-2723 (also taken for `a[::k] = array()`)
    let (start, step) :=
      if step < 0 then
        let stop' := start + 1
        (wrap (stop' + step * (len - 1) - 1), -step)
      else (start, step)
    let mem ← arrDelLoop size step len (len.toNat + 1) a.items start 0
    let cur := toU (start + len * step)
    let mem ← if cur < size then memmove mem (cur - len) cur (size - cur) else pure mem
    arrResize { a with items := mem } (size - len)
  else
    if needed ≠ len then
      throw (.valueError s!"attempt to assign array of size {needed} to extended slice of size {len}")
    return { a with items := storeLoop a.items start step src }

/-- `a[i] = v` / `del a[i]` for an int `i` (`array_ass_subscr`, arraymodule.c:2597-2615). -/
def arrAssIndex (a : Arr) (i : Int) (v : Option PyVal) : Py Arr := do
  let size : Int := a.items.length
  let i ← subIndex i
  let i := if i < 0 then i + size else i
  if i < 0 ∨ i ≥ size then throw (.indexError "array assignment index out of range")
  match v with
  | none => arrAssCore a i (i + 1) 1 1 none
  | some v =>
    let x ← tcSetitem a.tc true v
    return { a with items := a.items.set i.toNat x }

/-- `a[s] = value` / `del a[s]` for a slice (`array_ass_subscr`, arraymodule.c:2616-2662). -/
def arrAssSlice (a : Arr) (s : Slice) (value : SliceVal) : Py Arr := do
  let size : Int := a.items.length
  let (start, stop, step) ← sliceUnpack s
  let (start, stop, len) := adjustIndices size start stop step
  match value with
  | .delete => arrAssCore a start stop step len none
  | .arr o same =>
    if !same ∧ o.tc ≠ a.tc then throw (.typeError "bad argument type for built-in operation")
    arrAssCore a start stop step len (some o.items)
  | .other t => throw (.typeError s!"can only assign array (not \"{t}\") to array slice")

/-- `<descr>_compareitems` (arraymodule.c:644-654, the `DEFINE_COMPAREITEMS` macro): the
sign of the first difference in the first `length` items, 0 if none. -/
def compareItems (a b : List Int) : Nat → Int
  | 0 => 0
  | length + 1 =>
    match a, b with
    | x :: xs, y :: ys => if x ≠ y then (if x < y then -1 else 1) else compareItems xs ys length
    | _, _ => 0

/-- The generic search of `array_richcompare` (arraymodule.c:865-883): the first
position where the items differ, or `none`. -/
def arrFirstDiff (v w : Arr) : Nat → Int → Py (Option (PyVal × PyVal))
  | 0, _ => .ok none
  | fuel + 1, i =>
    if i < v.items.length ∧ i < w.items.length then
      match v.get i, w.get i with
      | .error e, _ => .error e
      | _, .error e => .error e
      | .ok vi, .ok wi =>
        if pvEq vi wi then arrFirstDiff v w fuel (i + 1) else .ok (some (vi, wi))
    else .ok none

/-- The `switch` on sizes in `array_richcompare` (arraymodule.c:886-901). -/
def sizeCmp (op : CmpOp) (vs ws : Int) : Bool :=
  match op with
  | .lt => vs < ws | .le => vs ≤ ws | .eq => true | .ne => false | .gt => vs > ws | .ge => vs ≥ ws

/-- `array_richcompare` (arraymodule.c:816-923) for two arrays. A non-array operand
gives `NotImplemented` (:826-827). -/
def arrRich (op : CmpOp) (v w : Arr) : Py Bool :=
  let vs : Int := v.items.length
  let ws : Int := w.items.length
  if vs ≠ ws ∧ (op = .eq ∨ op = .ne) then .ok (op = .ne)
  else if v.tc = w.tc ∧ v.tc.hasCompare then
    let result := compareItems v.items w.items (min v.items.length w.items.length)
    if result = 0 then .ok (sizeCmp op vs ws)
    else .ok (match op with
      | .lt => result < 0 | .le => result ≤ 0 | .eq => result = 0
      | .ne => result ≠ 0 | .gt => result > 0 | .ge => result ≥ 0)
  else
    match arrFirstDiff v w (v.items.length + 1) 0 with
    | .error e => .error e
    | .ok none => .ok (sizeCmp op vs ws)
    | .ok (some (vi, wi)) =>
      match op with
      | .eq => .ok false
      | .ne => .ok true
      | op => pvRich op vi wi

/-! ### Bytes, files, unicode -/

/-- The bytes of one item, little-endian two's complement. -/
def itemBytes (tc : TC) (x : Int) : List Nat :=
  let n := tc.itemsize.toNat
  let u := (x % 2 ^ (8 * n)).toNat
  (List.range n).map (fun i => (u >>> (8 * i)) % 256)

/-- The little-endian value of a list of bytes. -/
def leValue : List Nat → Nat
  | [] => 0
  | b :: bs => b + 256 * leValue bs

/-- The item stored in `bs`. -/
def itemOfBytes (tc : TC) (bs : List Nat) : Int :=
  let u : Int := leValue bs
  if tc.isSigned || tc == .u then
    (if u ≥ 2 ^ (8 * tc.itemsize.toNat - 1) then u - 2 ^ (8 * tc.itemsize.toNat) else u)
  else u

/-- Split into `n`-byte chunks. -/
def chunks (n : Nat) (bs : List Nat) (fuel : Nat) : List (List Nat) :=
  match fuel with
  | 0 => []
  | fuel + 1 => if bs.isEmpty then [] else bs.take n :: chunks n (bs.drop n) fuel

/-- `a.tobytes()` (`array_array_tobytes_impl`, arraymodule.c:1844-1853): the buffer. -/
def arrToBytes (a : Arr) : List Nat := a.items.flatMap (itemBytes a.tc)

/-- `frombytes` (arraymodule.c:1786-1817): `bufItemsize` is the buffer's `itemsize`. -/
def arrFromBytes (a : Arr) (bs : List Nat) (bufItemsize : Int) : Py Arr := do
  let itemsize := a.tc.itemsize
  if bufItemsize ≠ 1 then throw (.typeError "a bytes-like object is required")
  let n : Int := bs.length
  if n % itemsize ≠ 0 then throw (.valueError "bytes length not a multiple of item size")
  let n := n / itemsize
  if n > 0 then
    let old : Int := a.items.length
    if n > ssizeMax - old ∨ old + n > ssizeMax / itemsize then throw memoryError
    let a' ← arrResize a (old + n)
    let new := (chunks itemsize.toNat bs bs.length).map (itemOfBytes a.tc)
    return { a' with items := memcpy a'.items old new }
  return a

/-- What `f.read(nbytes)` returned. -/
inductive ReadResult where
  | bytes (bs : List Nat)
  | notBytes
  | raises (e : PyExc)

/-- `a.fromfile(f, n)` (`array_array_fromfile_impl`, arraymodule.c:1613-1661): `read`
is `f.read`. The items read are kept when `EOFError` is raised. -/
def arrFromFile (a : Arr) (read : Int → ReadResult) (n : Int) : Py Unit × Arr :=
  match asSsize n with
  | .error e => (.error e, a)
  | .ok n =>
    if n < 0 then (.error (.valueError "negative count"), a)
    else if n > ssizeMax / a.tc.itemsize then (.error memoryError, a)
    else
      let nbytes := n * a.tc.itemsize
      match read nbytes with
      | .raises e => (.error e, a)
      | .notBytes => (.error (.typeError "read() didn't return bytes"), a)
      | .bytes bs =>
        match arrFromBytes a bs 1 with
        | .error e => (.error e, a)
        | .ok a' =>
          if (bs.length : Int) ≠ nbytes then
            (.error (.named "EOFError" "read() didn't return enough bytes"), a')
          else (.ok (), a')

/-- The arguments of the `f.write` calls of `a.tofile(f)`
(`array_array_tofile_impl`, arraymodule.c:1676-1710): 64 KiB blocks. -/
def arrToFile (a : Arr) : List (List Nat) :=
  let bytes := arrToBytes a
  let nbytes : Int := bytes.length
  let blocksize : Int := 65536
  let nblocks := (nbytes + blocksize - 1) / blocksize
  if a.items.length = 0 then []
  else (List.range nblocks.toNat).map (fun (i : Nat) =>
    let start := (i : Int) * blocksize
    let size := if start + blocksize > nbytes then nbytes - start else blocksize
    (bytes.drop start.toNat).take size.toNat)

/-- The loop of `a.fromlist(list)`: `setitem` at `pos`, `pos + 1`, ... -/
def fromListLoop (tc : TC) : List PyVal → Int → List Int → Py (List Int)
  | [], _, items => .ok items
  | v :: vs, pos, items =>
    match tcSetitem tc true v with
    | .error e => .error e
    | .ok x => fromListLoop tc vs (pos + 1) (items.set pos.toNat x)

/-- `a.fromlist(list)` (`array_array_fromlist_impl`, arraymodule.c:1724-1752): all or
nothing, but a failure leaves the `allocated` of the first resize behind. `.inr t`
is an argument of another type. The size-changed check needs `__index__` to mutate
the list. -/
def arrFromList (a : Arr) (list : List PyVal ⊕ String) : Py Unit × Arr :=
  match list with
  | .inr _ => (.error (.typeError "arg must be list"), a)
  | .inl vs =>
    let n : Int := vs.length
    if n > 0 then
      let old : Int := a.items.length
      match arrResize a (old + n) with
      | .error e => (.error e, a)
      | .ok a' =>
        match fromListLoop a.tc vs old a'.items with
        | .ok items => (.ok (), { a' with items })
        | .error e =>
          match arrResize a' old with
          | .ok a'' => (.error e, a'')
          | .error _ => (.error e, a')
    else (.ok (), a)

/-- `a.tolist()` (`array_array_tolist_impl`, arraymodule.c:1764-1783). -/
def arrToList (a : Arr) : Py (List PyVal) := a.items.mapM (tcGetitem a.tc)

/-- `a.fromunicode(ustr)` (`array_array_fromunicode_impl`, arraymodule.c:1869-1916). -/
def arrFromUnicode (a : Arr) (ustr : List Nat) : Py Arr := do
  if a.tc ≠ .u ∧ a.tc ≠ .w then
    throw (.valueError "fromunicode() may only be called on unicode type arrays ('u' or 'w')")
  let old : Int := a.items.length
  if a.tc = .u then
    if ustr.length > 0 then
      let a' ← arrResize a (old + ustr.length)
      return { a' with items := memcpy a'.items old (ustr.map (fun (c : Nat) => (c : Int))) }
    return a
  else
    let a' ← arrResize a (old + ustr.length)
    -- `PyUnicode_AsUCS4(ustr, ob_item + old_size, ustr_length, 0)` refuses a NULL
    -- target with `PyErr_BadInternalCall`; the impl ignores the failure, so the
    -- method returns None with an exception set, which `_Py_CheckFunctionResult`
    -- turns into this `SystemError` (an `assert` in a debug build).
    if !a'.hasBuf then
      throw (.named "SystemError"
        "<method 'fromunicode' of 'array.array' objects> returned a result with an exception set")
    return { a' with items := memcpy a'.items old (ustr.map (fun (c : Nat) => (c : Int))) }

/-- A 32-bit unit with its bytes reversed. -/
def swap32 (u : Int) : Int :=
  (u % 256) * 16777216 + ((u / 256) % 256) * 65536 + ((u / 65536) % 256) * 256 + (u / 16777216) % 256

/-- `PyUnicode_DecodeUTF32Stateful` with `byteorder == 0` and strict errors
(Objects/unicodeobject.c), the native-order decoding of `a.tounicode()`, on the
items as native 32-bit units. A leading U+FEFF is a byte order mark: it is
skipped, and its swapped form selects the opposite byte order for what follows.
Surrogates and values above U+10FFFF are errors. The message of
`UnicodeDecodeError` is not modelled. -/
def decodeUTF32Native (us : List Int) : Py (List Nat) :=
  let (body, big) := match us with
    | 65279 :: rest => (rest, false)
    | 4294836224 :: rest => (rest, true)
    | us => (us, false)
  let cps := if big then body.map swap32 else body
  if cps.any (fun x => x > 1114111 ∨ (55296 ≤ x ∧ x ≤ 57343)) then
    .error (.named "UnicodeDecodeError" "~utf-32")
  else .ok (cps.map Int.toNat)

/-- `a.tounicode()` (`array_array_tounicode_impl`, arraymodule.c:1929-1946).
`PyUnicode_FromWideChar` (`u`) takes every code point; `w` decodes UTF-32. -/
def arrToUnicode (a : Arr) : Py (List Nat) := do
  if a.tc ≠ .u ∧ a.tc ≠ .w then
    throw (.valueError "tounicode() may only be called on unicode type arrays ('u' or 'w')")
  if a.tc = .u then
    match a.items.find? (fun x => x < 0 ∨ x > 1114111) with
    | some x =>
      throw (.valueError s!"~character U+{x} is not in range [U+0000; U+10ffff]")
    | none => return a.items.map Int.toNat
  else decodeUTF32Native a.items

/-- `a.__sizeof__()` (`array_array___sizeof___impl`, arraymodule.c:1955-1961):
`_PyObject_SIZE(type)` plus the allocated items. -/
def arrSizeof (a : Arr) (basicsize : Int) : Int := basicsize + a.allocated * a.tc.itemsize

/-- `a.byteswap()` (`array_array_byteswap_impl`, arraymodule.c:1518-1565): every item
with its bytes reversed. -/
def arrByteswap (a : Arr) : Arr :=
  { a with items := a.items.map (fun x => itemOfBytes a.tc (itemBytes a.tc x).reverse) }

/-- `a.reverse()` (`array_array_reverse_impl`, arraymodule.c:1575-1596): swap with
two cursors. -/
def arrReverseLoop : Nat → List Int → Int → Int → List Int
  | 0, l, _, _ => l
  | fuel + 1, l, p, q =>
    if p < q then
      let tmp := ix l p
      arrReverseLoop fuel ((l.set p.toNat (ix l q)).set q.toNat tmp) (p + 1) (q - 1)
    else l

def arrReverse (a : Arr) : Arr :=
  let n : Int := a.items.length
  if n > 1 then { a with items := arrReverseLoop a.items.length a.items 0 (n - 1) } else a

/-! ### Machine formats, pickling -/

/-- `typecode_to_mformat_code` (arraymodule.c:2002-2086) on a little-endian machine. -/
def mformatOf : TC → Int
  | .b => 1 | .B => 0
  | .u | .w => 20
  | .f => 14 | .d => 16
  | .h => 4 | .H => 2
  | .i => 8 | .I => 6
  | .l | .q => 12 | .L | .Q => 10

/-- `mformat_descriptors` (arraymodule.c:1966-1989): size, signed, big-endian. The
sizes of the UTF rows, 4 and 8, are what the source has. -/
def mformatDescr (c : Int) : Nat × Bool × Bool :=
  match c with
  | 0 => (1, false, false) | 1 => (1, true, false)
  | 2 => (2, false, false) | 3 => (2, false, true)
  | 4 => (2, true, false) | 5 => (2, true, true)
  | 6 => (4, false, false) | 7 => (4, false, true)
  | 8 => (4, true, false) | 9 => (4, true, true)
  | 10 => (8, false, false) | 11 => (8, false, true)
  | 12 => (8, true, false) | 13 => (8, true, true)
  | 14 => (4, false, false) | 15 => (4, false, true)
  | 16 => (8, false, false) | 17 => (8, false, true)
  | 18 => (4, false, false) | 19 => (4, false, true)
  | 20 => (8, false, false) | 21 => (8, false, true)
  | _ => (0, false, false)

/-- `iter(a)` as an iterable: an unreadable item ends it with its exception. -/
def arrItems (a : Arr) : PyIterable PyVal :=
  let rec go : List Int → List PyVal
    | [] => []
    | x :: xs =>
      match tcGetitem a.tc x with
      | .ok v => v :: go xs
      | .error _ => []
  let rec firstErr : List Int → Option PyExc
    | [] => none
    | x :: xs =>
      match tcGetitem a.tc x with
      | .ok _ => firstErr xs
      | .error e => some e
  .iter (go a.items) (firstErr a.items)

/-- The `initial` argument of `array_new`. -/
inductive Init where
  | none
  | list (vs : List PyVal)
  | tuple (vs : List PyVal)
  | bytes (bs : List Nat)
  | str (cps : List Nat)
  | arr (a : Arr)
  | iter (src : PyIterable PyVal)

/-- `array_new` (arraymodule.c:2798-2978) once `PyArg_ParseTuple("C|O:array")` has given
the typecode character `c`. `tname` is the type being instantiated. -/
def arrNew (tname : String) (c : Char) (initial : Init) : Py Arr :=
  let isUnicode := c == 'u' || c == 'w'
  let bad : Py Unit :=
    if isUnicode then .ok ()
    else match initial with
      | .str _ => .error (.typeError s!"cannot use a str to initialize an array with typecode '{c}'")
      | .arr o =>
        if o.tc == .u || o.tc == .w then
          .error (.typeError s!"cannot use a unicode array to initialize an array with typecode '{c}'")
        else .ok ()
      | _ => .ok ()
  match bad with
  | .error e => .error e
  | .ok () =>
    -- which initialisers go through `PyObject_GetIter`
    let viaIter : Option (PyIterable PyVal) := match initial with
      | .iter src => some src
      | .arr o => if c == o.tc.code then none else some (arrItems o)
      | _ => none
    match viaIter with
    | some (.notIterable t) => .error (notIterableErr t)
    | it =>
      match TC.all.find? (fun t => t.code == c) with
      | none => .error (.valueError "bad typecode (must be b, B, u, w, h, H, i, I, l, L, q, Q, f or d)")
      | some tc =>
        let init' := if it.isSome then Init.none else initial
        let len : Int := match init' with
          | .list vs | .tuple vs => vs.length
          | .arr o => o.items.length
          | _ => 0
        match newArr tname tc len with
        | .error e => .error e
        | .ok a =>
          let r : Py Arr := match init' with
            | .list vs | .tuple vs =>
              match vs.mapM (tcSetitem tc true) with
              | .ok xs => .ok { a with items := xs }
              | .error e => .error e
            | .bytes bs => arrFromBytes a bs 1
            | .str cps =>
              if c == 'u' then
                if cps.length > 0 then
                  .ok { a with items := cps.map (fun (c : Nat) => (c : Int)), hasBuf := true, allocated := cps.length }
                else .ok a
              else .ok { a with items := cps.map (fun (c : Nat) => (c : Int)), hasBuf := true, allocated := cps.length }
            | .arr o => if len > 0 then .ok { a with items := o.items } else .ok a
            | _ => .ok a
          match r, it with
          | .error e, _ => .error e
          | .ok a, some src =>
            match arrIterExtend a src with
            | (a, none) => .ok a
            | (_, some e) => .error e
          | .ok a, none => .ok a

/-- `make_array` (arraymodule.c:2110-2137): `array_new(arraytype, (typecode, items))`. -/
def makeArray (tname : String) (c : Char) (items : Init) : Py Arr := arrNew tname c items

/-- `big` endian bytes to code points for the slow path of the reconstructor. -/
def utf32Units (bs : List Nat) (big : Bool) : List Nat :=
  (chunks 4 bs bs.length).map (fun c => leValue (if big then c.reverse else c))

/-- `PyUnicode_DecodeUTF32` (strict): code points, or `UnicodeDecodeError`. -/
def decodeUTF32 (bs : List Nat) (big : Bool) : Py (List Nat) :=
  if bs.length % 4 ≠ 0 then .error (.named "UnicodeDecodeError" "~truncated data")
  else
    let us := utf32Units bs big
    if us.any (fun u => u > 1114111 ∨ (55296 ≤ u ∧ u ≤ 57343)) then
      .error (.named "UnicodeDecodeError" "~bad code point")
    else .ok us

/-- `PyUnicode_DecodeUTF16` (strict). -/
def decodeUTF16 (bs : List Nat) (big : Bool) : Py (List Nat) :=
  if bs.length % 2 ≠ 0 then .error (.named "UnicodeDecodeError" "~truncated data")
  else
    let units := (chunks 2 bs bs.length).map (fun c => leValue (if big then c.reverse else c))
    let rec go : List Nat → Nat → Py (List Nat)
      | [], _ => .ok []
      | _, 0 => .error .modelFuel
      | u :: us, fuel + 1 =>
        if u < 55296 ∨ u > 57343 then
          match go us fuel with
          | .ok r => .ok (u :: r)
          | e => e
        else if u ≥ 56320 then .error (.named "UnicodeDecodeError" "~illegal encoding")
        else
          match us with
          | v :: rest =>
            if 56320 ≤ v ∧ v ≤ 57343 then
              match go rest fuel with
              | .ok r => .ok ((65536 + (u - 55296) * 1024 + (v - 56320)) :: r)
              | e => e
            else .error (.named "UnicodeDecodeError" "~illegal UTF-16 surrogate")
          | [] => .error (.named "UnicodeDecodeError" "~unexpected end of data")
    go units (units.length + 1)

/-- `array._array_reconstructor(arraytype, typecode, mformat_code, items)`
(`array__array_reconstructor_impl`, arraymodule.c:2156-2360), with `items` bytes and
`arraytype` a subclass of `array.array` named `tname`. The checks of `arraytype` and
of `items` being bytes are the arguments' types here. -/
def reconstruct (tname : String) (typecode : Char) (mformat : Int) (items : List Nat) : Py Arr :=
  match TC.all.find? (fun t => t.code == typecode) with
  | none => .error (.valueError "second argument must be a valid type code")
  | some tc =>
    if mformat < 0 ∨ mformat > 21 then
      .error (.valueError "third argument must be a valid machine format code.")
    else if mformat = mformatOf tc then makeArray tname typecode (.bytes items)
    else
      let (msize, msigned, mbig) := mformatDescr mformat
      if items.length % msize ≠ 0 then
        .error (.valueError "string length not a multiple of item size")
      else if mformat = 14 ∨ mformat = 15 then
        let vals := (chunks 4 items items.length).map (fun c =>
          PyVal.float (floatToDouble (leValue (if mformat = 15 then c.reverse else c))))
        makeArray tname typecode (.list vals)
      else if mformat = 16 ∨ mformat = 17 then
        let vals := (chunks 8 items items.length).map (fun c =>
          PyVal.float (leValue (if mformat = 17 then c.reverse else c)))
        makeArray tname typecode (.list vals)
      else if mformat = 18 ∨ mformat = 19 then
        match decodeUTF16 items (mformat = 19) with
        | .error e => .error e
        | .ok s => makeArray tname typecode (.str s)
      else if mformat = 20 ∨ mformat = 21 then
        match decodeUTF32 items (mformat = 21) with
        | .error e => .error e
        | .ok s => makeArray tname typecode (.str s)
      else
        -- the last descriptor with this integer size and signedness
        let tc' := (TC.all.filter (fun t => t.isInteger && t.itemsize == (msize : Int) &&
          t.isSigned == msigned)).getLast?.getD tc
        let vals := (chunks msize items items.length).map (fun c =>
          let u : Int := leValue (if mbig then c.reverse else c)
          PyVal.int (if msigned ∧ u ≥ 2 ^ (8 * msize - 1) then u - 2 ^ (8 * msize) else u))
        makeArray tname tc'.code (.list vals)

/-- The result of `a.__reduce_ex__(protocol)` (`array_array___reduce_ex___impl`,
arraymodule.c:2364-2440), without the `__dict__`. -/
inductive Reduced where
  /-- `(type(a), (typecode, list), dict)`. -/
  | asList (tname : String) (c : Char) (items : List PyVal)
  /-- `(_array_reconstructor, (type(a), typecode, mformat_code, bytes), dict)`. -/
  | asBytes (tname : String) (c : Char) (mformat : Int) (bytes : List Nat)

def arrReduceEx (a : Arr) (protocol : PyVal) : Py Reduced :=
  match protocol with
  | .int p =>
    match asLongV (.int p) with
    | .error e => .error e
    | .ok p =>
      if p < 3 then
        match arrToList a with
        | .ok vs => .ok (.asList a.tname a.tc.code vs)
        | .error e => .error e
      else .ok (.asBytes a.tname a.tc.code (mformatOf a.tc) (arrToBytes a))
  | _ => .error (.typeError "__reduce_ex__ argument should be an integer")

/-- The `repr` of the list or string inside `repr(a)`, with `frepr` the repr of a
float (the shortest round-trip digits belong to `Binary64`). -/
def pvRepr (frepr : Nat → String) : PyVal → String
  | .float b => frepr b
  | .int n => toString n
  | v => v.typeName

/-- `repr(a)` (`array_repr`, arraymodule.c:2495-2520); `srepr` is `repr` of a str. -/
def arrRepr (frepr : Nat → String) (srepr : List Nat → String) (a : Arr) : Py String := do
  let c := a.tc.code
  if a.items.length = 0 then return s!"{a.tname}('{c}')"
  if a.tc = .u ∨ a.tc = .w then
    let s ← arrToUnicode a
    return s!"{a.tname}('{c}', {srepr s})"
  let vs ← arrToList a
  let body := ", ".intercalate (vs.map (pvRepr frepr))
  return s!"{a.tname}('{c}', [{body}])"

/-- The fields of `memoryview(a)` (`array_buffer_getbuf`, arraymodule.c:2750-2787):
format, itemsize, length in items, nbytes; the array gains an export. -/
def arrGetBuf (a : Arr) : (String × Int × Int × Int) × Arr :=
  let n : Int := a.items.length
  ((a.tc.format, a.tc.itemsize, n, n * a.tc.itemsize), { a with exports := a.exports + 1 })

/-- `array_buffer_relbuf` (arraymodule.c:2791-2795). -/
def arrRelBuf (a : Arr) : Arr := { a with exports := a.exports - 1 }

/-- `a.buffer_info()[1]` (`array_array_buffer_info_impl`, arraymodule.c:1466-1490).
The address is the only other field; it is 0 exactly when `ob_item` is NULL. -/
def arrBufferInfo (a : Arr) : Bool × Int := (a.hasBuf, a.items.length)

/-! ### Iterators -/

/-- `arrayiterobject`: `index`, and whether `ao` is still set. -/
structure ArrIter where
  index : Int
  live : Bool
  deriving Repr, DecidableEq

/-- `array_iter` (arraymodule.c:3101-3120). -/
def arrIter : ArrIter := ⟨0, true⟩

/-- `arrayiter_next` (arraymodule.c:3123-3140). -/
def arrIterNext (a : Arr) (it : ArrIter) : Py (Option PyVal) × ArrIter :=
  if !it.live then (.ok none, it)
  else if it.index < a.items.length then
    match a.get it.index with
    | .ok v => (.ok (some v), { it with index := it.index + 1 })
    | .error e => (.error e, { it with index := it.index + 1 })
  else (.ok none, { it with live := false })

/-- `it.__reduce__()` (`array_arrayiterator___reduce___impl`, arraymodule.c:3177-3187):
`(iter, ((),))` once exhausted, else `(iter, (a,), index)`. -/
def arrIterReduce (it : ArrIter) : Option Int := if it.live then some it.index else none

/-- `it.__setstate__(state)` (`array_arrayiterator___setstate___impl`,
arraymodule.c:3199-3216). -/
def arrIterSetstate (a : Arr) (it : ArrIter) (state : Int) : Py ArrIter := do
  let index ← asSsize state
  if it.live then
    let n : Int := a.items.length
    let index := if index < 0 then 0 else if index > n then n else index
    return { it with index }
  return it

end PyLean.Sequences
