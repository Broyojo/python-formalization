import PyLean.Registry
import PyLean.LongObj.BoolObj

/-! Statements and registry entries for conversions, `hash`, `bit_length`, `bit_count`
and `bool`. -/

namespace PyLean.LongObj

open PyLean PyLean.Registry PyLean.MathInt

/-- Every `PyLong_From*` of a 32 or 64 bit C integer builds the canonical object. -/
def FromCCanonical : Prop :=
  (∀ x : Int, x.natAbs ≤ 2 ^ 64 → fromCInt x = .ofInt x) ∧
  (∀ x : Nat, x ≤ 2 ^ 64 → fromCUInt x = .ofInt x)

theorem fromCCanonical_proven : FromCCanonical :=
  ⟨fun _ h => fromCInt_spec h, fun _ h => fromCUInt_spec h⟩

/-- `PyLong_AsLongAndOverflow`: the value in range, else `-1` and the sign. -/
def AsLongAndOverflowExact : Prop :=
  ∀ a : Int, asLongAndOverflow (.ofInt a) =
    if -(2 ^ 63 : Int) ≤ a ∧ a < 2 ^ 63 then (a, 0) else (-1, if a < 0 then -1 else 1)

theorem asLongAndOverflowExact_proven : AsLongAndOverflowExact := asLongAndOverflow_spec

/-- `PyLong_AsLong`, `PyLong_AsInt` and `PyLong_AsSsize_t` are exact on their type and
raise `OverflowError` outside it, for all ints. -/
def AsSignedExact : Prop :=
  ∀ a : Int,
    asLong (.ofInt a) = (if -(2 ^ 63 : Int) ≤ a ∧ a < 2 ^ 63 then .ok a
      else .error (.overflowError "Python int too large to convert to C long")) ∧
    asCInt (.ofInt a) = (if -(2 ^ 31 : Int) ≤ a ∧ a < 2 ^ 31 then .ok a
      else .error (.overflowError "Python int too large to convert to C int")) ∧
    asSsize (.ofInt a) = (if -(2 ^ 63 : Int) ≤ a ∧ a < 2 ^ 63 then .ok a
      else .error (.overflowError "Python int too large to convert to C ssize_t"))

theorem asSignedExact_proven : AsSignedExact := fun a =>
  ⟨asLong_spec a, asCInt_spec a, asSsize_spec a⟩

/-- `PyLong_AsUnsignedLong` and `PyLong_AsSize_t` reject negative values, are exact below
`2**64`, and raise `OverflowError` above it. -/
def AsUnsignedExact : Prop :=
  ∀ a : Int,
    asUnsignedLong (.ofInt a) =
      (if a < 0 then .error (.overflowError "can't convert negative value to unsigned int")
      else if a < 2 ^ 64 then .ok a.toNat
      else .error (.overflowError "Python int too large to convert to C unsigned long")) ∧
    asSizeT (.ofInt a) =
      (if a < 0 then .error (.overflowError "can't convert negative value to size_t")
      else if a < 2 ^ 64 then .ok a.toNat
      else .error (.overflowError "Python int too large to convert to C size_t"))

theorem asUnsignedExact_proven : AsUnsignedExact := fun a => ⟨asUnsignedLong_spec a, asSizeT_spec a⟩

/-- The `*Mask` conversions are reduction modulo `2**64`, for all ints. -/
def AsMaskExact : Prop := ∀ a : Int, asUnsignedMask (.ofInt a) = (a % 2 ^ 64).toNat

theorem asMaskExact_proven : AsMaskExact := asUnsignedMask_spec

/-- `long_sign` is the sign of the value. -/
def LongSignExact : Prop :=
  ∀ a : Int, longSign (.ofInt a) = if a < 0 then -1 else if a = 0 then 0 else 1

theorem longSignExact_proven : LongSignExact := longSign_spec

/-- `_PyLong_NumBits` and `int.bit_length` are the bit length of the magnitude. -/
def NumBitsExact : Prop := ∀ a : Int, numBits (.ofInt a) = bitLength a.natAbs

theorem numBitsExact_proven : NumBitsExact := numBits_spec

/-- `long_hash` follows the documented numeric hash for all ints, on both paths. -/
def LongHashExact : Prop := ∀ a : Int, longHash (.ofInt a) = pyHash a

theorem longHashExact_proven : LongHashExact := longHash_spec

/-- `int.bit_count` is the number of ones in the magnitude. -/
def BitCountExact : Prop :=
  ∀ a : Int, bitCount (.ofInt a) = popK (bitLength a.natAbs) a.natAbs

theorem bitCountExact_proven : BitCountExact := bitCount_spec

/-- `bool(...)` through `tp_new` and vectorcall agree for every argument list and every
truth oracle in which `False` is false. -/
def BoolTwinsAgree : Prop :=
  ∀ (α : Type) (isTrue : α → Py Bool) (false_ : α), isTrue false_ = .ok false →
    ∀ (args : List α) (kw : Bool), boolNew isTrue false_ args kw = boolVectorcall isTrue args kw

theorem boolTwinsAgree_proven : BoolTwinsAgree := fun _ t f h a k => boolNew_eq_vectorcall t f h a k

/-- `repr`, and `~` with its deprecation. -/
def BoolInvertExact : Prop :=
  boolRepr true = "True" ∧ boolRepr false = "False" ∧
  ∀ v : Bool, boolInvert false v = .ok (-(BoolOperand.b v).toInt - 1) ∧
    boolInvert true v = .error (.named "DeprecationWarning" boolInvertMsg)

theorem boolInvertExact_proven : BoolInvertExact :=
  ⟨rfl, rfl, boolInvert_spec⟩

/-- `&`, `|`, `^` on two `bool`s return a `bool` agreeing with the `int` operator; with an
`int` operand they return that `int` operator's result. -/
def BoolOpsExact : Prop :=
  ∀ (op : BitOp) (x y : Bool),
    boolOp op (.b x) (.b y) = .ok (.b (op.bool x y)) ∧
    (∀ i, bitZ (BoolOperand.b (op.bool x y)).toInt i =
      op.bool (bitZ (BoolOperand.b x).toInt i) (bitZ (BoolOperand.b y).toInt i))

theorem boolOpsExact_proven : BoolOpsExact := fun op x y =>
  ⟨boolOp_bool op x y, boolOp_agrees op x y⟩

def entriesConv : List Entry := [
  { id := "longobj-from-c", pyFile := "Objects/longobject.c"
    pyFns := ["PyLong_FromLong", "PyLong_FromUnsignedLong", "PyLong_FromUnsignedLongLong", "PyLong_FromSize_t",
      "PyLong_FromLongLong", "PyLong_FromSsize_t", "PyLong_FromVoidPtr", "PyLong_FromInt32", "PyLong_FromUInt32",
      "PyLong_FromInt64", "PyLong_FromUInt64"]
    statement := "Every PyLong_From* of a 32 or 64 bit C integer builds the canonical object of its value."
    source := "C API docs: Integer Objects", status := .proven
    prop := ``FromCCanonical, thm := some ``fromCCanonical_proven },
  { id := "longobj-as-long-overflow", pyFile := "Objects/longobject.c"
    pyFns := ["PyLong_AsLongAndOverflow", "PyLong_AsLongLongAndOverflow"]
    statement := "PyLong_AsLongAndOverflow returns the value with overflow 0 when it fits long, otherwise -1 with overflow the sign."
    source := "comment at longobject.c:501-509", status := .proven
    prop := ``AsLongAndOverflowExact, thm := some ``asLongAndOverflowExact_proven
    notes := "The two functions are identical on LP64 except | versus + on a shifted value. Non-int arguments through __index__ are not modelled." },
  { id := "longobj-as-signed", pyFile := "Objects/longobject.c"
    pyFns := ["PyLong_AsLong", "PyLong_AsInt", "PyLong_AsSsize_t"]
    statement := "PyLong_AsLong, PyLong_AsInt and PyLong_AsSsize_t are exact on their C type and raise OverflowError with their message outside it."
    source := "C API docs: Integer Objects", status := .proven
    prop := ``AsSignedExact, thm := some ``asSignedExact_proven },
  { id := "longobj-as-unsigned", pyFile := "Objects/longobject.c"
    pyFns := ["PyLong_AsUnsignedLong", "PyLong_AsSize_t"]
    statement := "PyLong_AsUnsignedLong and PyLong_AsSize_t raise OverflowError on negative values and above 2**64 - 1 and are exact otherwise."
    source := "C API docs: Integer Objects", status := .proven
    prop := ``AsUnsignedExact, thm := some ``asUnsignedExact_proven },
  { id := "longobj-as-mask", pyFile := "Objects/longobject.c"
    pyFns := ["_PyLong_AsUnsignedLongMask", "PyLong_AsUnsignedLongMask", "_PyLong_AsUnsignedLongLongMask",
      "PyLong_AsUnsignedLongLongMask"]
    statement := "The mask conversions return the value modulo 2**64 for every int."
    source := "C API docs: PyLong_AsUnsignedLongMask", status := .proven
    prop := ``AsMaskExact, thm := some ``asMaskExact_proven },
  { id := "longobj-sign", pyFile := "Objects/longobject.c"
    pyFns := ["long_sign", "_PyLong_Sign", "PyLong_GetSign", "PyLong_IsPositive", "PyLong_IsNegative", "PyLong_IsZero"]
    statement := "long_sign is -1, 0 or 1 by the sign of the value."
    source := "C API docs: PyLong_GetSign", status := .proven
    prop := ``LongSignExact, thm := some ``longSignExact_proven },
  { id := "longobj-num-bits", pyFile := "Objects/longobject.c"
    pyFns := ["_PyLong_NumBits", "int_bit_length_impl"]
    statement := "_PyLong_NumBits and int.bit_length are the bit length of the magnitude, for all ints."
    source := "int.bit_length docs", status := .proven
    prop := ``NumBitsExact, thm := some ``numBitsExact_proven },
  { id := "longobj-hash", pyFile := "Objects/longobject.c", pyFns := ["long_hash"]
    statement := "hash(a) is sign(a) * (abs(a) % (2**61 - 1)), with -1 replaced by -2, for all ints, on the compact and digit paths."
    source := "stdtypes: Hashing of numeric types", status := .proven
    prop := ``LongHashExact, thm := some ``longHashExact_proven
    notes := "Proves the rotation argument of the comment at longobject.c:3609-3633." },
  { id := "longobj-bit-count", pyFile := "Objects/longobject.c"
    pyFns := ["int_bit_count_impl", "popcount_digit"]
    statement := "int.bit_count is the number of ones in the binary representation of the absolute value."
    source := "int.bit_count docs", status := .proven
    prop := ``BitCountExact, thm := some ``bitCountExact_proven },
  { id := "bool-twins", pyFile := "Objects/boolobject.c"
    pyFns := ["bool_new", "bool_vectorcall", "PyBool_FromLong"]
    statement := "bool(...) through tp_new and through vectorcall agree for every argument list and truth oracle."
    source := "implementation twins", status := .proven
    prop := ``BoolTwinsAgree, thm := some ``boolTwinsAgree_proven },
  { id := "bool-repr-invert", pyFile := "Objects/boolobject.c", pyFns := ["bool_repr", "bool_invert"]
    statement := "repr gives True or False; ~v is -int(v)-1, or the DeprecationWarning when warnings are errors."
    source := "boolobject.c:14-17, :71-84", status := .proven
    prop := ``BoolInvertExact, thm := some ``boolInvertExact_proven },
  { id := "bool-ops", pyFile := "Objects/boolobject.c", pyFns := ["bool_and", "bool_or", "bool_xor"]
    statement := "&, | and ^ on two bools return a bool agreeing with the int operator on 0 and 1."
    source := "stdtypes: boolean type", status := .proven
    prop := ``BoolOpsExact, thm := some ``boolOpsExact_proven }
]

end PyLean.LongObj
