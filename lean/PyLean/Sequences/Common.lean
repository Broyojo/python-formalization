import PyLean.Core
import PyLean.RangeSlice.Model

/-!
Shared vocabulary for the `list` (`Objects/listobject.c`), `array.array`
(`Modules/arraymodule.c`) and `collections.deque`
(`Modules/_collectionsmodule.c`) models, CPython 3.15.2.

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
parameters), Objects/longobject.c:748-749. -/
def asSsize (x : Int) : Py Int :=
  if ssizeMin ≤ x ∧ x ≤ ssizeMax then .ok x
  else .error (.overflowError "Python int too large to convert to C ssize_t")

/-- `PyNumber_AsSsize_t(item, exc)` on an exact int, Objects/abstract.c:1468-1510:
`exc` with "cannot fit 'int' into an index-sized integer". -/
def asSsizeExc (mk : String → PyExc) (x : Int) : Py Int :=
  if ssizeMin ≤ x ∧ x ≤ ssizeMax then .ok x
  else .error (mk "cannot fit 'int' into an index-sized integer")

/-- Subscript conversion (`list_subscript`, `array_subscr`, `PyObject_GetItem`
for `sq_item`): `PyNumber_AsSsize_t(item, PyExc_IndexError)`. -/
def subIndex (x : Int) : Py Int := asSsizeExc .indexError x

/-- Repeat counts (`sequence_repeat`, Objects/abstract.c:1157-1172,
used for both `*` and `*=`): `PyNumber_AsSsize_t(n, PyExc_OverflowError)`. -/
def repeatCount (x : Int) : Py Int := asSsizeExc .overflowError x

/-- `slice_index` / `_PyEval_SliceIndexNotNone` on an int: saturates. -/
def sliceIndex (x : Int) : Int := RangeSlice.clampSsize x

/-- `valid_index(i, limit)`: `(size_t)i < (size_t)limit` for `0 <= limit`. -/
def validIndex (i limit : Int) : Bool := decide (0 ≤ i ∧ i < limit)

/-- An iterable argument: not iterable (`PyObject_GetIter` fails on an object of
this type), or an iterator that yields `xs` and then ends with the exception
`e` (`none`: plain exhaustion). -/
inductive PyIterable (α : Type) where
  | notIterable (tname : String)
  | iter (xs : List α) (e : Option PyExc)
  deriving Repr

/-- `PyObject_GetIter` on a non-iterable (Objects/abstract.c:2813). -/
def notIterableErr (tname : String) : PyExc := .typeError s!"'{tname}' object is not iterable"

/-- A rich comparison operator. -/
inductive CmpOp where
  | lt | le | eq | ne | gt | ge
  deriving Repr, DecidableEq, Inhabited

/-! ## List helpers

Sequences hold arbitrary Python objects, so the list helpers and the `list` and
`deque` models are generic in the element type `α`. Rich comparison of elements
is an explicit parameter of the functions that need it. -/

section
variable {α : Type} [Inhabited α]

/-- `l[i]` (0-based), the default element past the end. -/
def ix (l : List α) (i : Int) : α := l.getD i.toNat default

/-- `take i l ++ x :: drop i l`. -/
def insAt (l : List α) (i : Nat) (x : α) : List α := l.take i ++ x :: l.drop i

/-- `memmove(mem + dst, mem + src, cnt)` on a buffer of `mem.length` items;
undefined if either range leaves the buffer. Reads see the old contents. -/
def memmove (mem : List α) (dst src cnt : Int) : Py (List α) :=
  if 0 ≤ dst ∧ 0 ≤ src ∧ 0 ≤ cnt ∧ dst + cnt ≤ mem.length ∧ src + cnt ≤ mem.length then
    .ok (mem.take dst.toNat ++ (mem.drop src.toNat).take cnt.toNat ++ mem.drop (dst + cnt).toNat)
  else .error (cUB "memmove out of bounds")

theorem ix_getElem (l : List α) (i : Nat) (h : i < l.length) : ix l i = l[i] := by
  unfold ix
  rw [List.getD_eq_getElem?_getD, show ((i : Int)).toNat = i by omega, List.getElem?_eq_getElem h]
  rfl

theorem ix_mem (l : List α) (k : Int) (h0 : 0 ≤ k) (h1 : k < l.length) : ix l k ∈ l := by
  have h : k.toNat < l.length := by omega
  have e := ix_getElem l k.toNat h
  rw [show ((k.toNat : Nat) : Int) = k by omega] at e
  rw [e]
  exact List.getElem_mem h

/-- The first position at or after `i` whose element satisfies `p`, scanning
`fuel` positions. -/
def firstFrom (p : α → Bool) (l : List α) : Nat → Nat → Option Nat
  | _, 0 => none
  | i, fuel + 1 => if i < l.length then (if p (ix l i) then some i else firstFrom p l (i + 1) fuel) else none

end

end PyLean.Sequences

namespace PyLean.Sequences

theorem iteT {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]
theorem iteF {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

end PyLean.Sequences
