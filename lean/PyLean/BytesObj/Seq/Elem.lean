import PyLean.Core
import PyLean.Sequences.Common

/-!
Shared vocabulary for the `tuple` and `list` models, CPython 3.14.7.

The element type is abstract, as the C code is: `tuple` and `list` never look
inside an element except through `PyObject_RichCompare`, `PyObject_Hash` and
`PyObject_Repr`. `ElemOps α ρ` packages what the model needs, where `ρ` is the
type of the objects a rich comparison may return (`bool` or anything else).

The difftest instantiates it with `DEl` (`Seq/Diff.lean`): ints plus objects
with odd comparisons, whose Python twins are in `difftest/bytesobj_diff.py`.

As in `Sequences`, memory is unbounded (`malloc` does not fail) and the
*explicit* overflow checks that raise `MemoryError` are modelled.
-/

namespace PyLean.BytesObj.Seq

open PyLean

abbrev cUB := PyLean.Sequences.cUB
abbrev memoryError := PyLean.Sequences.memoryError

/-- `PyErr_BadInternalCall()`. The message embeds `__FILE__:__LINE__`. -/
def systemError : PyExc := .named "SystemError" "~bad argument to internal function"

/-- `Py_LT`, `Py_LE`, `Py_EQ`, `Py_NE`, `Py_GT`, `Py_GE`. -/
inductive CmpOp where
  | lt | le | eq | ne | gt | ge
  deriving DecidableEq, Repr, Inhabited

/-- What the sequence code asks of its elements. -/
structure ElemOps (α ρ : Type) where
  /-- `v == w` on pointers. -/
  same : α → α → Bool
  /-- `PyObject_RichCompare(v, w, op)`. -/
  rich : CmpOp → α → α → Py ρ
  /-- `PyObject_IsTrue` with the `PyBool_Check` shortcut. -/
  truth : ρ → Py Bool
  /-- `Py_True` / `Py_False`. -/
  ofBool : Bool → ρ

variable {α ρ : Type}

/-- `PyObject_RichCompareBool(v, w, op)`, Objects/object.c:1119-1142: the
identity shortcut for `==` and `!=`, then `PyObject_RichCompare` and `IsTrue`. -/
def richBool (E : ElemOps α ρ) (op : CmpOp) (v w : α) : Py Bool :=
  if E.same v w && op == .eq then .ok true
  else if E.same v w && op == .ne then .ok false
  else
    match E.rich op v w with
    | .ok r => E.truth r
    | .error e => .error e

/-- `Py_RETURN_RICHCOMPARE(val1, val2, op)`, Include/object.h. -/
def cmpSizes (op : CmpOp) (a b : Int) : Bool :=
  match op with
  | .eq => decide (a = b)
  | .ne => decide (a ≠ b)
  | .lt => decide (a < b)
  | .gt => decide (a > b)
  | .le => decide (a ≤ b)
  | .ge => decide (a ≥ b)

/-- `PyObject_Length`-free reading of `a[i]`: the slot at a non-negative C index. -/
def slot (l : List α) (i : Int) : Option α := if 0 ≤ i then l[i.toNat]? else none

/-- `valid_index(i, limit)`, Objects/listobject.c:314-325: the unsigned compare
`(size_t) i < (size_t) limit`, for `0 <= limit`. -/
def validIndex (i limit : Int) : Bool := decide (i % (2 ^ 64 : Int) < limit % (2 ^ 64 : Int))

/-- The C cursor of a slice copy, `cur += (size_t)step`, reads `n` items. Every
read goes through `slot`, so a read outside the object is `cUB`, not a value. -/
def sliceLoop (l : List α) (step : Int) : Nat → Int → Py (List α)
  | 0, _ => .ok []
  | n + 1, cur =>
    match slot l cur with
    | some v =>
      match sliceLoop l step n (cur + step) with
      | .ok r => .ok (v :: r)
      | .error e => .error e
    | none => .error (cUB "read outside the items array")

end PyLean.BytesObj.Seq
