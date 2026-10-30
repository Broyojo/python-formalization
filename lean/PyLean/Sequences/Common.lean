import PyLean.Core
import PyLean.RangeSlice.Model

/-!
Shared vocabulary for the `list` (`Objects/listobject.c`), `array.array`
(`Modules/arraymodule.c`) and `collections.deque`
(`Modules/_collectionsmodule.c`) models, CPython 3.14.7.

* Elements are Python ints (`Int`) compared with `==`; rich comparison of
  ints never fails, so `PyObject_RichCompareBool` is `decide (a = b)`.
* Argument conversions are modelled exactly: Argument Clinic `Py_ssize_t`
  parameters (`PyLong_AsSsize_t`: `OverflowError`), `slice_index` /
  `_PyEval_SliceIndexNotNone` parameters (`PyNumber_AsSsize_t(v, NULL)`:
  saturating), subscripts (`PyNumber_AsSsize_t(v, PyExc_IndexError)`) and
  sequence repeat counts (`PyNumber_AsSsize_t(v, PyExc_OverflowError)`).
* Memory is unbounded: `malloc` never fails. The *explicit* overflow checks
  in the C code that raise `MemoryError` are modelled. (Allocation of a result
  larger than the machine's memory is outside the model; the differential
  tester never requests one.)
* C undefined behaviour the model can reach (a NULL dereference, a read of an
  unused deque slot, a `memmove` outside the buffer) is reported as `cUB`,
  which is not a Python outcome; properties show it never happens.
-/

namespace PyLean.Sequences

open PyLean

/-- C undefined behaviour reached by the model. Never a Python outcome. -/
def cUB (what : String) : PyExc := .named "CUndefinedBehaviour" what

/-- `MemoryError()` (`PyErr_NoMemory`); its `str()` is empty. -/
def memoryError : PyExc := .named "MemoryError" ""

/-- `PyLong_AsSsize_t` on an exact int (Argument Clinic `Py_ssize_t`
parameters), Objects/longobject.c:668-669. -/
def asSsize (x : Int) : Py Int :=
  if ssizeMin ≤ x ∧ x ≤ ssizeMax then .ok x
  else .error (.overflowError "Python int too large to convert to C ssize_t")

/-- `PyNumber_AsSsize_t(item, exc)` on an exact int, Objects/abstract.c:1458-1500:
`exc` with "cannot fit 'int' into an index-sized integer". -/
def asSsizeExc (mk : String → PyExc) (x : Int) : Py Int :=
  if ssizeMin ≤ x ∧ x ≤ ssizeMax then .ok x
  else .error (mk "cannot fit 'int' into an index-sized integer")

/-- Subscript conversion (`list_subscript`, `array_subscr`, `PyObject_GetItem`
for `sq_item`): `PyNumber_AsSsize_t(item, PyExc_IndexError)`. -/
def subIndex (x : Int) : Py Int := asSsizeExc .indexError x

/-- Repeat counts (`sequence_repeat`, Objects/abstract.c:1147-1162,
used for both `*` and `*=`): `PyNumber_AsSsize_t(n, PyExc_OverflowError)`. -/
def repeatCount (x : Int) : Py Int := asSsizeExc .overflowError x

/-- `slice_index` / `_PyEval_SliceIndexNotNone` on an int: saturates. -/
def sliceIndex (x : Int) : Int := RangeSlice.clampSsize x

/-- `valid_index(i, limit)`: `(size_t)i < (size_t)limit` for `0 <= limit`. -/
def validIndex (i limit : Int) : Bool := decide (0 ≤ i ∧ i < limit)

/-! ## List helpers -/

/-- `l[i]` (0-based, `Nat`), `0` past the end. -/
def ix (l : List Int) (i : Int) : Int := l.getD i.toNat 0

/-- `take i l ++ x :: drop i l`. -/
def insAt (l : List Int) (i : Nat) (x : Int) : List Int := l.take i ++ x :: l.drop i

/-- `memmove(mem + dst, mem + src, cnt)` on a buffer of `mem.length` items;
undefined if either range leaves the buffer. Reads see the old contents. -/
def memmove (mem : List Int) (dst src cnt : Int) : Py (List Int) :=
  if 0 ≤ dst ∧ 0 ≤ src ∧ 0 ≤ cnt ∧ dst + cnt ≤ mem.length ∧ src + cnt ≤ mem.length then
    .ok (mem.take dst.toNat ++ (mem.drop src.toNat).take cnt.toNat ++ mem.drop (dst + cnt).toNat)
  else .error (cUB "memmove out of bounds")

/-- Index of the first element equal to `x` at or after `i`, scanning `fuel`
positions. -/
def firstFrom (l : List Int) (x : Int) : Nat → Nat → Option Nat
  | _, 0 => none
  | i, fuel + 1 => if i < l.length then (if ix l i = x then some i else firstFrom l x (i + 1) fuel) else none

end PyLean.Sequences

namespace PyLean.Sequences

theorem iteT {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]
theorem iteF {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

end PyLean.Sequences
