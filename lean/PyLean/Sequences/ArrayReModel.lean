import PyLean.Sequences.ArrayModel

/-!
`array.array` operations whose item conversion runs Python code that can change the array
(`Modules/arraymodule.c`, CPython 3.15.2).

Every `*_setitem` but `u_setitem`/`w_setitem` converts its argument before it touches the
array: `PyArg_Parse` with `h`, `b`, `i`, `l` or `L` (`PyLong_AsLong`/`PyLong_AsLongLong`, which
call `__index__`), `_PyNumber_Index` for `I`, `L` and `Q`, `PyArg_Parse` with `f`/`D`
(`__float__`, `__index__`, `__complex__`) for the float and complex typecodes. That code can
clear, grow or export the array. The setitem then re-checks with `CHECK_ARRAY_BOUNDS`
(arraymodule.c:217-225): an index `>= 0` must still be inside the array and `ob_item`
non-NULL, else `IndexError`; a negative index is only a check and stores nothing.

`ReVal` is such an item: call `k` of its conversion (0 for the first) may change the array,
and what is left of the conversion is the plain value `tcSetitem` sees. `ArrayModel`'s
operations are the case of an item that leaves the array alone (`ReVal.pure`); the
theorems of `ArrayReentrant` show that they agree with these.

The `ins1` of 3.15.2 reads `n = Py_SIZE(self)` (:865) before its first `setitem` runs the
conversion (:870) and resizes to the stale `n + 1` (:873): after code that cleared the array
the resize allocates `n + 1` new items that nobody writes (uninitialised memory in CPython, 0
in the model, which pads with 0: `resized`), after code that grew it the grown items are cut
off (bugs/sequences-array-ins1-stale-size.yaml).
-/

namespace PyLean.Sequences

open PyLean

/-- An item whose conversion may run Python code that changes the array. `v k a` is call
`k` of the conversion (0 for the first) while the array is `a`: the array the code leaves,
and the plain value standing for the rest of the conversion. The plain value's own
conversion runs no more code: a `.user` whose method returned `r` (or raised: `Ret.raises`)
stands for the method's outcome. -/
abbrev ReVal := Nat → Arr → Arr × PyVal

/-- An item whose conversion leaves the array alone. -/
def ReVal.pure (v : PyVal) : ReVal := fun _ a => (a, v)

/-- What a `*_setitem(ap, i, v)` does once the conversion code has run and left the array
`a`: for `i >= 0` the conversion's own checks of `tcSetitem` with `CHECK_ARRAY_BOUNDS`
in its place (`idxOk`: `ob_item` is not NULL and `i < Py_SIZE(ap)`), then the store
`(... *)ap->ob_item)[i] = x`; for `i < 0` the check `tcCheck`, no store. -/
def storeAfter (a : Arr) (i : Int) (v : PyVal) : Arr × Py Unit :=
  if i < 0 then (a, tcCheck a.tc v)
  else
    match tcSetitem a.tc (a.hasBuf && decide (i < a.items.length)) v with
    | .error e => (a, .error e)
    | .ok x => ({ a with items := a.items.set i.toNat x }, .ok ())

/-- `(*ap->ob_descr->setitem)(ap, i, v)` (arraymodule.c:248-739) for an item whose
conversion is `conv`: the conversion first, then `storeAfter`. -/
def setitemRe (a : Arr) (i : Int) (conv : Arr → Arr × PyVal) : Arr × Py Unit :=
  let (a', pv) := conv a
  storeAfter a' i pv

/-- `ins1` (arraymodule.c:862-889) for an item whose conversion may change the array. The
size is read once, at :865, before the first `setitem(self, -1, v)` (:870) runs the code;
the resize to `n+1` (:873), the clipping of `where` (:876-882), the `memmove` (:884-887) and
the store `setitem(self, where, v)` (:888) all use that `n`. The array reached, and the
error. -/
def arrIns1Re (a : Arr) (where_ : Int) (v : ReVal) : Arr × Option PyExc :=
  let n : Int := a.items.length
  match setitemRe a (-1) (v 0) with
  | (a1, .error e) => (a1, some e)
  | (a1, .ok ()) =>
    match arrResize a1 (n + 1) with
    | .error e => (a1, some e)
    | .ok a2 =>
      let w := ins1Pos n where_
      match (if w ≠ n then memmove a2.items (w + 1) w (n - w) else .ok a2.items : Py (List Int)) with
      | .error e => (a2, some e)
      | .ok items =>
        match setitemRe { a2 with items } w (v 1) with
        | (a3, .error e) => (a3, some e)
        | (a3, .ok ()) => (a3, none)

/-- `a.append(v)` (`ins(self, Py_SIZE(self), v)`, arraymodule.c:1585-1589). -/
def arrAppendRe (a : Arr) (v : ReVal) : Arr × Option PyExc := arrIns1Re a a.items.length v

/-- `a.insert(i, v)` (`array_array_insert_impl`, :1542-1546, through `ins`, :1331-1336); the
index is converted by Argument Clinic before `v` is touched. -/
def arrInsertRe (a : Arr) (i : Int) (v : ReVal) : Arr × Option PyExc :=
  match asSsize i with
  | .error e => (a, some e)
  | .ok i => arrIns1Re a i v

/-- The loop of `array_iter_extend` (arraymodule.c:1232-1252): `ins1(self, Py_SIZE(self), v)`
per item, `Py_SIZE` read anew for each. -/
def arrIterItemsRe (a : Arr) : List ReVal → Arr × Option PyExc
  | [] => (a, none)
  | v :: vs =>
    match arrIns1Re a a.items.length v with
    | (a', none) => arrIterItemsRe a' vs
    | (a', some e) => (a', some e)

/-- `a.extend(iterable)` for an iterator that yields `xs` and then ends with `e`. -/
def arrIterExtendRe (a : Arr) (src : PyIterable ReVal) : Arr × Option PyExc :=
  match src with
  | .notIterable t => (a, some (notIterableErr t))
  | .iter xs e =>
    match arrIterItemsRe a xs with
    | (a, some err) => (a, some err)
    | (a, none) =>
      match e with
      | some .stopIteration => (a, none)
      | e => (a, e)

/-- `a[i] = v` for an int `i` (`array_ass_subscr`, arraymodule.c:2802-2822): the index is
normalised and checked against the size before `v` is converted, then
`(*self->ob_descr->setitem)(self, i, value)`. -/
def arrAssIndexRe (a : Arr) (i : Int) (v : ReVal) : Arr × Py Unit :=
  match subIndex i with
  | .error e => (a, .error e)
  | .ok i =>
    let i := if i < 0 then i + a.items.length else i
    if i < 0 ∨ i ≥ a.items.length then (a, .error (.indexError "array assignment index out of range"))
    else setitemRe a i (v 0)

/-- `array_ass_item` (arraymodule.c:1208-1219), the `sq_ass_item` slot, through which
`setarrayitem` (:1222-1229) stores. -/
def arrAssItemRe (a : Arr) (i : Int) (v : ReVal) : Arr × Py Unit :=
  if i < 0 ∨ i ≥ a.items.length then (a, .error (.indexError "array assignment index out of range"))
  else setitemRe a i (v 0)

/-! ### `fromlist` -/

/-- `array_resize(self, old_size)` after a failure of `fromlist` (arraymodule.c:1871, 1877):
its result is ignored, but a failing resize sets `BufferError`, which replaces the pending
exception. -/
def fromListRestore (a : Arr) (old : Int) (e : PyExc) : Py Unit × Arr :=
  match arrResize a old with
  | .ok a' => (.error e, a')
  | .error e' => (.error e', a)

/-- The loop of `array_array_fromlist_impl` (arraymodule.c:1867-1880) for a list of `X`s
whose conversion `conv x (a, l)` runs code that may change the array and the list: item `i`
is `PyList_GET_ITEM(list, i)` of the list as it is then, stored at `Py_SIZE(self) - n + i`
computed before the conversion runs; a failed store restores the old size; after each
store `n != PyList_GET_SIZE(list)` raises `RuntimeError` and restores. -/
def fromListReLoop {X : Type} (conv : X → Arr × List X → (Arr × List X) × PyVal)
    (n old : Int) : Nat → Int → Arr × List X → Py Unit × Arr × List X
  | 0, _, (a, l) => (.ok (), a, l)
  | fuel + 1, i, (a, l) =>
    if i < n then
      match l[i.toNat]? with
      -- unreachable: the size check below keeps `len(list) == n`
      | none => (.ok (), a, l)
      | some x =>
        let idx : Int := (a.items.length : Int) - n + i
        let ((a1, l1), pv) := conv x (a, l)
        match storeAfter a1 idx pv with
        | (a2, .error e) =>
          let (r, a3) := fromListRestore a2 old e
          (r, a3, l1)
        | (a2, .ok ()) =>
          if n ≠ l1.length then
            let (r, a3) := fromListRestore a2 old (.named "RuntimeError" "list changed size during iteration")
            (r, a3, l1)
          else fromListReLoop conv n old fuel (i + 1) (a2, l1)
    else (.ok (), a, l)

/-- `a.fromlist(list)` (`array_array_fromlist_impl`, arraymodule.c:1852-1883). `.inr t` is
an argument of another type. -/
def arrFromListRe {X : Type} (conv : X → Arr × List X → (Arr × List X) × PyVal)
    (a : Arr) (list : List X ⊕ String) : Py Unit × Arr :=
  match list with
  | .inr _ => (.error (.typeError "arg must be list"), a)
  | .inl l =>
    let n : Int := l.length
    if n > 0 then
      let old : Int := a.items.length
      match arrResize a (old + n) with
      | .error e => (.error e, a)
      | .ok a' =>
        let (r, a'', _) := fromListReLoop conv n old l.length 0 (a', l)
        (r, a'')
    else (.ok (), a)

/-- The conversion of a list of plain values, which changes nothing. -/
def pureConv : PyVal → Arr × List PyVal → (Arr × List PyVal) × PyVal := fun v s => (s, v)

/-! ### Searching with a comparison that runs Python code -/

/-- `PyObject_RichCompareBool(selfi, v, Py_EQ)` of `count`, `index`, `in` and `remove` for a
`v` whose `__eq__` runs Python code that may change the array: `cmp i a x` is the comparison
of item `i` (the loops compare each index at most once), read as `x`, while the array is `a`;
the array the code leaves, and the outcome (an exception of `__eq__` or of the truth test of
its result included). -/
abbrev ReCmp := Int → Arr → PyVal → Arr × Py Bool

/-- A comparison that leaves the array alone. -/
def ReCmp.pure (eqv : PyVal → Py Bool) : ReCmp := fun _ a x => (a, eqv x)

/-- An upper bound on the iterations of the search loops: each compares an index
`i < Py_SIZE(self) <= PY_SSIZE_T_MAX`. Running out is `PyExc.modelFuel`. -/
def searchFuel : Nat := 9223372036854775808

/-- The loop of `array_array_count_impl` (arraymodule.c:1354-1367):
`for (i = 0; i < Py_SIZE(self); i++)`, the size read anew before each item, the item read
with `getarrayitem` (:1358-1360) and compared (:1361-1366), whose code may change the array the
next test reads. -/
def countReLoop (cmp : ReCmp) : Nat → Int → Int → Arr → Arr × Py Int
  | 0, _, _, a => (a, .error .modelFuel)
  | fuel + 1, i, c, a =>
    if i < a.items.length then
      match a.get i with
      | .error e => (a, .error e)
      | .ok x =>
        match cmp i a x with
        | (a', .error e) => (a', .error e)
        | (a', .ok b) => countReLoop cmp fuel (i + 1) (if b then c + 1 else c) a'
    else (a, .ok c)

/-- `a.count(v)` (`array_array_count_impl`, arraymodule.c:1348-1369): the array the
comparisons leave, and the count. -/
def arrCountRe (cmp : ReCmp) (a : Arr) : Arr × Py Int := countReLoop cmp searchFuel 0 0 a

/-- The bound of `index`'s loop besides the size: `i < stop` (`some stop`), none for `in`
and `remove`. -/
def stopOk (stop : Option Int) (i : Int) : Bool :=
  match stop with
  | some s => decide (i < s)
  | none => true

/-- The scan of `array_array_index_impl` (arraymodule.c:1399-1415,
`for (i = start; i < stop && i < Py_SIZE(self); i++)`, "Use Py_SIZE() for every iteration in
case the array is mutated during PyObject_RichCompareBool()"), of `array_contains` (:1426-1432,
`cmp == 0 && i < Py_SIZE(self)`) and of `array_array_remove_impl` (:1451-1467): the size is
read anew before each item; `.ok (some i)` is the first match. -/
def scanRe (cmp : ReCmp) (stop : Option Int) : Nat → Int → Arr → Arr × Py (Option Int)
  | 0, _, a => (a, .error .modelFuel)
  | fuel + 1, i, a =>
    if stopOk stop i = true ∧ i < a.items.length then
      match a.get i with
      | .error e => (a, .error e)
      | .ok x =>
        match cmp i a x with
        | (a', .error e) => (a', .error e)
        | (a', .ok true) => (a', .ok (some i))
        | (a', .ok false) => scanRe cmp stop fuel (i + 1) a'
    else (a, .ok none)

/-- `a.index(v[, start[, stop]])` (`array_array_index_impl`, arraymodule.c:1386-1418): `start`
and `stop` are adjusted with the size at entry (:1390-1398; Argument Clinic's `slice_index`
accepts only ints, so no code runs before), then the scan. -/
def arrIndexRe (cmp : ReCmp) (a : Arr) (start stop : Option Int) : Arr × Py Int :=
  let n : Int := a.items.length
  let start := sliceIndex (start.getD 0)
  let stop := sliceIndex (stop.getD ssizeMax)
  let start := if start < 0 then (if start + n < 0 then 0 else start + n) else start
  let stop := if stop < 0 then stop + n else stop
  match scanRe cmp (some stop) searchFuel start a with
  | (a', .error e) => (a', .error e)
  | (a', .ok (some i)) => (a', .ok i)
  | (a', .ok none) => (a', .error (.valueError "array.index(x): x not in array"))

/-- `v in a` (`array_contains`, arraymodule.c:1421-1434). -/
def arrContainsRe (cmp : ReCmp) (a : Arr) : Arr × Py Bool :=
  match scanRe cmp none searchFuel 0 a with
  | (a', r) => (a', r.map Option.isSome)

/-- `a.remove(v)` (`array_array_remove_impl`, arraymodule.c:1446-1470): the match at `i`
is deleted with `array_del_slice(self, i, i+1)` from the array as the comparison left it
(:1461), which clips `i` to that array's size. -/
def arrRemoveRe (cmp : ReCmp) (a : Arr) : Arr × Py Unit :=
  match scanRe cmp none searchFuel 0 a with
  | (a', .error e) => (a', .error e)
  | (a', .ok (some i)) =>
    match arrDelSlice a' i (i + 1) with
    | .ok a'' => (a'', .ok ())
    | .error e => (a', .error e)
  | (a', .ok none) => (a', .error (.valueError "array.remove(x): x not in array"))

/-! ### Subscript keys -/

/-- The key of `a[key]`: an object with `__index__` (its value), a slice, or anything else. -/
inductive SubKey where
  | int (i : Int)
  | slice (s : PyLean.RangeSlice.Slice)
  | other

/-- `a[key]` (`array_subscr`, arraymodule.c:2730-2792): `PyIndex_Check` first, then
`PySlice_Check`, else `TypeError`. -/
def arrSubscr (a : Arr) : SubKey → Py (PyVal ⊕ Arr)
  | .int i => Sum.inl <$> arrGetItem a i
  | .slice s => Sum.inr <$> arrGetSlice a s
  | .other => .error (.typeError "array indices must be integers")

end PyLean.Sequences
