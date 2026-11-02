import PyLean.Core

/-!
Model of `bisect`: the pure-Python twin `Lib/bisect.py` and the C accelerator
`Modules/_bisectmodule.c` (CPython 3.15.2), over lists of `int` compared with `<`.

* `a` is a Python `list` of ints (`List Int`); its length is a `Py_ssize_t`, so
  `a.length ≤ ssizeMax` is a type invariant.
* `key=None` is `none`; a key function is a pure `Int → Int`. Raising key
  functions and mutation during comparison are out of scope.
* `lo` is a Python int; `hi` is `none` for `hi=None` (or omitted) and `some h`
  for an int.
-/

namespace PyLean.Accel

open PyLean

/-- `key(e)` when a key is given, `e` otherwise. -/
def applyKey (key : Option (Int → Int)) (e : Int) : Int :=
  match key with
  | none => e
  | some f => f e

/-- The `while lo < hi` loop shared by both twins. `probe mid` is the element
access `a[mid]` (whose failure modes differ between the twins) and `goRight v`
decides `lo = mid + 1` (otherwise `hi = mid`). Each iteration shrinks `hi - lo`,
so `fuel = hi - lo` is always enough; `modelFuel` is unreachable. -/
def bisectLoop (probe : Int → Py Int) (goRight : Int → Bool) : Nat → Int → Int → Py Int
  | 0, lo, hi => if lo < hi then .error .modelFuel else .ok lo
  | fuel + 1, lo, hi =>
    if lo < hi then do
      let mid := (lo + hi) / 2
      let v ← probe mid
      if goRight v then bisectLoop probe goRight fuel (mid + 1) hi
      else bisectLoop probe goRight fuel lo mid
    else .ok lo

/-! ### Pure-Python twin, `Lib/bisect.py` -/

/-- `a[i]` for an int `i ≥ 0` on a list (`list_subscript`, Objects/listobject.c):
the index is narrowed with `PyNumber_AsSsize_t(item, PyExc_IndexError)` and
then bounds-checked. -/
def pyIndex (a : List Int) (i : Int) : Py Int :=
  if i > ssizeMax then .error (.indexError "cannot fit 'int' into an index-sized integer")
  else if 0 ≤ i ∧ i < a.length then .ok (a.getD i.toNat 0)
  else .error (.indexError "list index out of range")

/-- `bisect_right(a, x, lo, hi, key=key)`, Lib/bisect.py:21-54. With a key the
comparison is `x < key(a[mid])` (:50), without one `x < a[mid]` (:43). -/
def pyBisectRight (a : List Int) (x lo : Int) (hi : Option Int) (key : Option (Int → Int)) : Py Int :=
  if lo < 0 then .error (.valueError "lo must be non-negative")
  else
    let hi := hi.getD a.length
    bisectLoop (fun mid => applyKey key <$> pyIndex a mid) (fun v => !decide (x < v))
      (hi - lo).toNat lo hi

/-- `bisect_left(a, x, lo, hi, key=key)`, Lib/bisect.py:74-107. The comparison
is `key(a[mid]) < x` (:103) or `a[mid] < x` (:96). -/
def pyBisectLeft (a : List Int) (x lo : Int) (hi : Option Int) (key : Option (Int → Int)) : Py Int :=
  if lo < 0 then .error (.valueError "lo must be non-negative")
  else
    let hi := hi.getD a.length
    bisectLoop (fun mid => applyKey key <$> pyIndex a mid) (fun v => decide (v < x))
      (hi - lo).toNat lo hi

/-- `list.insert(i, x)` (`list_insert_impl` → `ins1`, Objects/listobject.c):
`i` goes through the `Py_ssize_t` converter, then is clamped to `[0, len]`. -/
def listInsert (a : List Int) (i : Int) (x : Int) : Py (List Int) :=
  if i < ssizeMin ∨ i > ssizeMax then
    .error (.overflowError "Python int too large to convert to C ssize_t")
  else
    let n : Int := a.length
    let w := if i < 0 then max (i + n) 0 else min i n
    .ok (a.insertIdx w.toNat x)

/-- `insort_right(a, x, lo, hi, key=key)`, Lib/bisect.py:4-18: the final list. -/
def pyInsortRight (a : List Int) (x lo : Int) (hi : Option Int) (key : Option (Int → Int)) : Py (List Int) := do
  let i ← pyBisectRight a (applyKey key x) lo hi key
  listInsert a i x

/-- `insort_left(a, x, lo, hi, key=key)`, Lib/bisect.py:57-72: the final list. -/
def pyInsortLeft (a : List Int) (x lo : Int) (hi : Option Int) (key : Option (Int → Int)) : Py (List Int) := do
  let i ← pyBisectLeft a (applyKey key x) lo hi key
  listInsert a i x

/-! ### C accelerator, `Modules/_bisectmodule.c` -/

/-- Argument Clinic's `lo: Py_ssize_t(allow_negative=False) = 0`
(clinic/_bisectmodule.c.h:84-101): `_PyNumber_Index`, `PyLong_AsSsize_t`, then
the converter's own check. Since 3.15 this refusal happens here, while parsing
`lo`, so before `hi` is converted, and its message differs from `bisect.py`'s. -/
def cConvLo (lo : Int) : Py Int :=
  if lo < ssizeMin ∨ lo > ssizeMax then
    .error (.overflowError "Python int too large to convert to C ssize_t")
  else if lo < 0 then .error (.valueError "lo cannot be negative")
  else .ok lo

/-- `hi: Py_ssize_t(c_default='-1', accept={int, NoneType}) = None`:
`_Py_convert_optional_to_ssize_t` (Python/modsupport.c:15-35) leaves the
default `-1` for `None` and otherwise calls
`PyNumber_AsSsize_t(obj, PyExc_OverflowError)`. -/
def cConvHi : Option Int → Py Int
  | none => .ok (-1)
  | some h =>
    if h < ssizeMin ∨ h > ssizeMax then
      .error (.overflowError "cannot fit 'int' into an index-sized integer")
    else .ok h

/-- `sq_item(list, mid)` = `list_item` (Objects/listobject.c:696-714). In the
loop `0 ≤ mid`, and `valid_index` is an unsigned `mid < len`. -/
def cIndex (a : List Int) (i : Int) : Py Int :=
  if 0 ≤ i ∧ i < a.length then .ok (a.getD i.toNat 0)
  else .error (.indexError "list index out of range")

/-- `internal_bisect_right`, Modules/_bisectmodule.c:53-145, on already
converted `Py_ssize_t` arguments. 3.15 removed the `lo < 0` check here: it moved
into the converter, `cConvLo`, so `0 ≤ lo` on entry. `hi == -1` means "use
`len(a)`" (:60-64). `mid = ((size_t)lo + hi) / 2` (:78) cannot wrap since
`0 ≤ lo < hi ≤ PY_SSIZE_T_MAX`. The same-type fast path (:98-125) and the generic
path (:126-129) compute the same `item < litem` for ints. -/
def cInternalRight (a : List Int) (x lo hi : Int) (key : Option (Int → Int)) : Py Int :=
  let hi := if hi = -1 then (a.length : Int) else hi
  bisectLoop (fun mid => applyKey key <$> cIndex a mid) (fun v => !decide (x < v))
    (hi - lo).toNat lo hi

/-- `internal_bisect_left`, Modules/_bisectmodule.c:233-325 (`litem < item`). -/
def cInternalLeft (a : List Int) (x lo hi : Int) (key : Option (Int → Int)) : Py Int :=
  let hi := if hi = -1 then (a.length : Int) else hi
  bisectLoop (fun mid => applyKey key <$> cIndex a mid) (fun v => decide (v < x))
    (hi - lo).toNat lo hi

/-- `_bisect.bisect_right`, Modules/_bisectmodule.c:147-175, with its clinic
wrapper (clinic/_bisectmodule.c.h:84-113 parses `lo` before `hi`). -/
def cBisectRight (a : List Int) (x lo : Int) (hi : Option Int) (key : Option (Int → Int)) : Py Int := do
  let lo ← cConvLo lo
  let hi ← cConvHi hi
  cInternalRight a x lo hi key

/-- `_bisect.bisect_left`, Modules/_bisectmodule.c:328-356. -/
def cBisectLeft (a : List Int) (x lo : Int) (hi : Option Int) (key : Option (Int → Int)) : Py Int := do
  let lo ← cConvLo lo
  let hi ← cConvHi hi
  cInternalLeft a x lo hi key

/-- `PyList_Insert(a, index, x)` for `0 ≤ index` (`ins1` clamps to `len`). -/
def cListInsert (a : List Int) (i : Int) (x : Int) : List Int :=
  a.insertIdx (min i a.length).toNat x

/-- `_bisect.insort_right`, Modules/_bisectmodule.c:177-230: the final list. -/
def cInsortRight (a : List Int) (x lo : Int) (hi : Option Int) (key : Option (Int → Int)) : Py (List Int) := do
  let lo ← cConvLo lo
  let hi ← cConvHi hi
  let i ← cInternalRight a (applyKey key x) lo hi key
  return cListInsert a i x

/-- `_bisect.insort_left`, Modules/_bisectmodule.c:359-411: the final list. -/
def cInsortLeft (a : List Int) (x lo : Int) (hi : Option Int) (key : Option (Int → Int)) : Py (List Int) := do
  let lo ← cConvLo lo
  let hi ← cConvHi hi
  let i ← cInternalLeft a (applyKey key x) lo hi key
  return cListInsert a i x

end PyLean.Accel
