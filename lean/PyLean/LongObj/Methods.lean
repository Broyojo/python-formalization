import PyLean.Registry
import PyLean.LongObj.BoolObj

/-!
The small `int` methods and getters, `sys.int_info`, the compact-value API and the
export/writer API of `Objects/longobject.c`.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt PyLean.Registry

/-- `long_long(v)`, longobject.c:5735-5743, `long_long_meth`, :6507-6510 and
`long_long_getter`, :6513-6516: the value, as an exact `int`. `_PyLong_Copy`,
longobject.c:222-248, for a subclass instance gives the same digits. -/
def longLong (v : Long) : Long := v

/-- `long_get0`, longobject.c:6073-6076 (`int.imag`). -/
def longGet0 : Long := ⟨false, []⟩
/-- `long_get1`, longobject.c:6079-6082 (`int.denominator`). -/
def longGet1 : Long := ⟨false, [1]⟩

/-- `int___getnewargs___impl`, longobject.c:6066-6070: a one-element tuple. -/
def getNewArgs (v : Long) : List Long := [longLong v]

/-- `int_as_integer_ratio_impl`, longobject.c:6361-6369. -/
def asIntegerRatio (v : Long) : Long × Long := (longLong v, longGet1)

/-- `int_is_integer_impl`, longobject.c:6526-6530. -/
def isInteger (_ : Long) : Bool := true

/-- `tp_basicsize` and `tp_itemsize` of `int`: `offsetof(PyLongObject, ob_digit)` and
`sizeof(digit)`, on a 64-bit build without `Py_GIL_DISABLED`. -/
def intBasicSize : Nat := 24
def intItemSize : Nat := 4

/-- `int___sizeof___impl`, longobject.c:6274-6281. -/
def intSizeof (v : Long) : Nat := intBasicSize + intItemSize * max v.ds.length 1

/-- The values `PyLong_GetInfo`, longobject.c:6721-6748, stores in `sys.int_info`:
`bits_per_digit`, `sizeof_digit`, `default_max_str_digits`,
`str_digits_check_threshold`. -/
def intInfo : List Nat := [30, 4, 4300, 640]

/-- `PyUnstable_Long_IsCompact`, longobject.c:6776-6778. -/
def unstableIsCompact (v : Long) : Bool := v.isCompact
/-- `PyUnstable_Long_CompactValue`, longobject.c:6783-6785. -/
def unstableCompactValue (v : Long) : Int := v.medium

/-- What `PyLong_Export`, longobject.c:6883-6922, fills in: a value that fits `int64_t`,
or the sign and the digit array. -/
inductive LongExport where
  | value (x : Int)
  | digits (negative : Bool) (ds : List Nat)
  deriving Repr, DecidableEq

def longExport (v : Long) : LongExport :=
  let (x, overflow) := asLongAndOverflow v
  if overflow = 0 then .value x
  else .digits v.neg (if v.ds.length = 0 then [0] else v.ds)

/-- `PyLongWriter_Create`, longobject.c:6939-6961, filled with `ds`, then
`PyLongWriter_Finish`, :6978-7009. -/
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

/-- `PyLongWriter_Create` then `PyLongWriter_Finish`, for every digit array the caller
may write: an empty count is the ValueError of :6941-6944, too many digits is
`long_alloc`'s OverflowError, and otherwise Finish's `long_normalize` and
`maybe_small_long` (:7006) give the canonical object of the value, whatever leading zero
digits the caller left and whatever sign it asked for zero. Digits below `2**30` are the
API's documented precondition. -/
def WriterExact : Prop :=
  (∀ n : Bool, longWriter n [] = .error (.valueError "ndigits must be positive")) ∧
  (∀ (n : Bool) (ds : List Nat), maxLongDigits < ds.length →
    longWriter n ds = .error (.overflowError "too many digits in integer")) ∧
  ∀ (negative : Bool) (ds : List Nat), ds ≠ [] → IsDigits ds → ds.length ≤ maxLongDigits →
    longWriter negative ds = .ok (Long.ofInt (if negative then -(val ds : Int) else val ds))

theorem writerExact_proven : WriterExact := by
  refine ⟨writerRejectsEmpty_proven, fun n ds h => ?_, fun negative ds hne hd hs => ?_⟩
  · have h0 : ¬ ds.length = 0 := by omega
    simp only [longWriter, h0, ite_false, longAlloc, if_pos h]
  · have h0 : ¬ ds.length = 0 := fun h => hne (List.eq_nil_of_length_eq_zero h)
    simp only [longWriter, h0, ite_false]
    rw [longAlloc_ok hs]
    simp only
    rw [digitsOf_normalize hd]
    by_cases hv : val ds = 0
    · rw [hv]
      have e : digitsOf 0 = [] := digitsOf_eq_nil.2 rfl
      cases negative <;> simp [e, Long.ofInt]
    · have hemp : (digitsOf (val ds)).isEmpty = false := by
        cases hh : digitsOf (val ds) with
        | nil => exact absurd (digitsOf_eq_nil.1 hh) hv
        | cons _ _ => rfl
      cases negative
      · simp [hemp, Long.ofInt_natCast]
      · simp only [hemp, ite_true]
        rw [Long.ofInt_neg_natCast (by omega)]
        rfl

def entriesMethods : List Entry := [
  { id := "longobj-export-writer", pyFile := "Objects/longobject.c"
    pyFns := ["PyLongWriter_Create", "PyLongWriter_Finish"]
    statement := "PyLong_Export followed by the PyLongWriter API round-trips every int."
    source := "C API docs: Export API", status := .proven
    prop := ``ExportRoundTrip, thm := some ``exportRoundTrip_proven },
  { id := "longobj-writer", pyFile := "Objects/longobject.c"
    pyFns := ["PyLongWriter_Create", "PyLongWriter_Finish"]
    statement := "PyLongWriter_Create rejects ndigits <= 0 with ValueError and too many digits with OverflowError; PyLongWriter_Finish returns the canonical int of the written digits and sign, normalizing leading zero digits and negative zero."
    source := "C API docs: PyLongWriter_Finish (\"normalizes the digits\")", status := .proven
    prop := ``WriterExact, thm := some ``writerExact_proven
    notes := "Smoke-tested through _testcapi.pylongwriter_create on 3.15.2, with trailing zero digits and negative zero. The Py_DEBUG check for uninitialized digits (:6983-7003) is compiled out of release builds." }
]

end PyLean.LongObj
