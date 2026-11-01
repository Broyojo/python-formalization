import PyLean.Registry
import PyLean.LongObj.BoolObj

/-!
The small `int` methods and getters, `sys.int_info`, the compact-value API and the
export/writer API of `Objects/longobject.c`.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt PyLean.Registry

/-- `long_long(v)`, longobject.c:5636-5644, `long_long_meth`, :6400-6403 and
`long_long_getter`, :6406-6409: the value, as an exact `int`. `_PyLong_Copy`,
longobject.c:217-243, for a subclass instance gives the same digits. -/
def longLong (v : Long) : Long := v

/-- `long_get0`, longobject.c:5969-5972 (`int.imag`). -/
def longGet0 : Long := ⟨false, []⟩
/-- `long_get1`, longobject.c:5975-5978 (`int.denominator`). -/
def longGet1 : Long := ⟨false, [1]⟩

/-- `int___getnewargs___impl`, longobject.c:5962-5966: a one-element tuple. -/
def getNewArgs (v : Long) : List Long := [longLong v]

/-- `int_as_integer_ratio_impl`, longobject.c:6263-6274. -/
def asIntegerRatio (v : Long) : Long × Long := (longLong v, longGet1)

/-- `int_is_integer_impl`, longobject.c:6418-6422. -/
def isInteger (_ : Long) : Bool := true

/-- `tp_basicsize` and `tp_itemsize` of `int`: `offsetof(PyLongObject, ob_digit)` and
`sizeof(digit)`, on a 64-bit build without `Py_GIL_DISABLED`. -/
def intBasicSize : Nat := 24
def intItemSize : Nat := 4

/-- `int___sizeof___impl`, longobject.c:6177-6184. -/
def intSizeof (v : Long) : Nat := intBasicSize + intItemSize * max v.ds.length 1

/-- The values `PyLong_GetInfo`, longobject.c:6613-6640, stores in `sys.int_info`:
`bits_per_digit`, `sizeof_digit`, `default_max_str_digits`,
`str_digits_check_threshold`. -/
def intInfo : List Nat := [30, 4, 4300, 640]

/-- `PyUnstable_Long_IsCompact`, longobject.c:6668-6670. -/
def unstableIsCompact (v : Long) : Bool := v.isCompact
/-- `PyUnstable_Long_CompactValue`, longobject.c:6675-6677. -/
def unstableCompactValue (v : Long) : Int := v.medium

/-- What `PyLong_Export`, longobject.c:6771-6810, fills in: a value that fits `int64_t`,
or the sign and the digit array. -/
inductive LongExport where
  | value (x : Int)
  | digits (negative : Bool) (ds : List Nat)
  deriving Repr, DecidableEq

def longExport (v : Long) : LongExport :=
  let (x, overflow) := asLongAndOverflow v
  if overflow = 0 then .value x
  else .digits v.neg (if v.ds.length = 0 then [0] else v.ds)

/-- `PyLongWriter_Create`, longobject.c:6827-6849, filled with `ds`, then
`PyLongWriter_Finish`, :6866-6875. -/
def longWriter (negative : Bool) (ds : List Nat) : Py Long :=
  if ds.length = 0 then .error (.valueError "ndigits must be positive")
  else
    match longAlloc ds.length with
    | .error e => .error e
    | .ok _ =>
      let n := normalize ds
      .ok ⟨negative && !n.isEmpty, n⟩

/-! ## Statements -/

/-- The method family returns the documented values for every int. -/
def IntMethodsExact : Prop :=
  ∀ a : Int,
    (longLong (.ofInt a)).toInt = a ∧ longGet0.toInt = 0 ∧ longGet1.toInt = 1 ∧
    (getNewArgs (.ofInt a)).map Long.toInt = [a] ∧
    ((asIntegerRatio (.ofInt a)).1.toInt = a ∧ (asIntegerRatio (.ofInt a)).2.toInt = 1) ∧
    isInteger (.ofInt a) = true

theorem intMethodsExact_proven : IntMethodsExact := fun a =>
  ⟨Long.toInt_ofInt a, by decide, by decide, by simp [getNewArgs, longLong, Long.toInt_ofInt],
   ⟨Long.toInt_ofInt a, by show longGet1.toInt = 1; decide⟩, rfl⟩

/-- `int.__sizeof__` counts the digits, with at least one even for zero. -/
def IntSizeofExact : Prop :=
  ∀ a : Int, intSizeof (.ofInt a) = 24 + 4 * max (digitCount a.natAbs) 1

theorem intSizeofExact_proven : IntSizeofExact := fun a => by
  simp only [intSizeof, intBasicSize, intItemSize, Long.ofInt, length_digitsOf]

/-- `sys.int_info` holds the build constants this model assumes. -/
def IntInfoExact : Prop := intInfo = [30, 4, 4300, 640]

theorem intInfoExact_proven : IntInfoExact := rfl

/-- The compact API answers for exactly the one-digit values. -/
def UnstableCompactExact : Prop :=
  ∀ a : Int, unstableIsCompact (.ofInt a) = decide (a.natAbs < 2 ^ 30) ∧
    (a.natAbs < 2 ^ 30 → unstableCompactValue (.ofInt a) = a)

theorem unstableCompactExact_proven : UnstableCompactExact := fun a =>
  ⟨Long.isCompact_ofInt a, Long.medium_ofInt⟩

/-- `PyLong_Export` followed by the writer API gives the same int back: a value that
fits comes back directly, and anything else through its digits. -/
def ExportRoundTrip : Prop :=
  ∀ a : Int, digitCount a.natAbs ≤ maxLongDigits →
    match longExport (.ofInt a) with
    | .value x => x = a
    | .digits n ds => longWriter n ds = .ok (.ofInt a)

theorem exportRoundTrip_proven : ExportRoundTrip := fun a hs => by
  by_cases h : -(2 ^ 63 : Int) ≤ a ∧ a < 2 ^ 63
  · have e : asLongAndOverflow (.ofInt a) = (a, 0) := by
      rw [asLongAndOverflow_spec, if_pos h]
    simp [longExport, e]
  · have e : asLongAndOverflow (.ofInt a) = (-1, if a < 0 then -1 else 1) := by
      rw [asLongAndOverflow_spec, if_neg h]
    have hs0 := overflow_sign_ne a
    simp only [longExport, e, if_neg hs0]
    have hne : digitsOf a.natAbs ≠ [] := by rw [Ne, digitsOf_eq_nil]; omega
    have hlen : ¬ (digitsOf a.natAbs).length = 0 := by
      intro h0; exact hne (List.eq_nil_of_length_eq_zero h0)
    have hds : (Long.ofInt a).ds = digitsOf a.natAbs := rfl
    have hneg : (Long.ofInt a).neg = decide (a < 0) := rfl
    simp only [hds, hneg, hlen, ite_false, longWriter]
    rw [longAlloc_ok (by rw [length_digitsOf]; exact hs)]
    simp only
    rw [digitsOf_normalize (digitsOf_digits _), val_digitsOf]
    have hemp : (digitsOf a.natAbs).isEmpty = false := by
      cases hh : digitsOf a.natAbs with
      | nil => exact absurd hh hne
      | cons _ _ => rfl
    simp [hemp, Long.ofInt]

/-- `PyLongWriter_Create` rejects an empty digit count. -/
def WriterRejectsEmpty : Prop :=
  ∀ n : Bool, longWriter n [] = .error (.valueError "ndigits must be positive")

theorem writerRejectsEmpty_proven : WriterRejectsEmpty := fun _ => rfl

def entriesMethods : List Entry := [
  { id := "longobj-methods", pyFile := "Objects/longobject.c"
    pyFns := ["long_long", "long_long_meth", "long_long_getter", "long_get0", "long_get1",
      "int___getnewargs___impl", "int_as_integer_ratio_impl", "int_is_integer_impl", "_PyLong_Copy"]
    statement := "int(a), a.real, a.numerator, a.conjugate(), a.imag == 0, a.denominator == 1, a.as_integer_ratio() == (a, 1), a.is_integer() and a.__getnewargs__() == (a,) for every int."
    source := "stdtypes: additional methods on integer types", status := .proven
    prop := ``IntMethodsExact, thm := some ``intMethodsExact_proven },
  { id := "longobj-sizeof", pyFile := "Objects/longobject.c", pyFns := ["int___sizeof___impl"]
    statement := "a.__sizeof__() is the base size plus one digit size per digit, with at least one digit."
    source := "comment at longobject.c:6180-6181", status := .proven
    prop := ``IntSizeofExact, thm := some ``intSizeofExact_proven },
  { id := "longobj-int-info", pyFile := "Objects/longobject.c", pyFns := ["PyLong_GetInfo"]
    statement := "sys.int_info is (30, 4, 4300, 640) on this build."
    source := "sys.int_info docs", status := .proven
    prop := ``IntInfoExact, thm := some ``intInfoExact_proven },
  { id := "longobj-unstable-compact", pyFile := "Objects/longobject.c"
    pyFns := ["PyUnstable_Long_IsCompact", "PyUnstable_Long_CompactValue"]
    statement := "PyUnstable_Long_IsCompact is exactly abs(a) < 2**30, and then PyUnstable_Long_CompactValue is a."
    source := "C API docs", status := .proven
    prop := ``UnstableCompactExact, thm := some ``unstableCompactExact_proven },
  { id := "longobj-export-writer", pyFile := "Objects/longobject.c"
    pyFns := ["PyLong_Export", "PyLongWriter_Create", "PyLongWriter_Finish"]
    statement := "PyLong_Export followed by the PyLongWriter API round-trips every int."
    source := "C API docs: Export API", status := .proven
    prop := ``ExportRoundTrip, thm := some ``exportRoundTrip_proven },
  { id := "longobj-writer-empty", pyFile := "Objects/longobject.c", pyFns := ["PyLongWriter_Create"]
    statement := "PyLongWriter_Create raises ValueError for ndigits <= 0."
    source := "longobject.c:6829-6832", status := .proven
    prop := ``WriterRejectsEmpty, thm := some ``writerRejectsEmpty_proven }
]

end PyLean.LongObj
