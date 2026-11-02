import PyLean.Core

/-!
`PyLong_GetSign`, `PyLong_IsPositive`, `PyLong_IsNegative`, `PyLong_IsZero`
(Objects/longobject.c:900-962), CPython 3.15.2, on an object that is an int (its value and the
sign bits of `lv_tag`) or not (its type name).

Type invariant (`_PyLong_SetSignAndDigitCount`, Include/internal/pycore_long.h): the sign bits
`lv_tag & SIGN_MASK` are 0 for a positive value, `SIGN_ZERO` = 1 for zero and `SIGN_NEGATIVE` = 2
for a negative value.
-/

namespace PyLean.LongObj.SignApi

inductive Obj where
  | int (v : Int) (signBits : Nat)
  | other (tyName : String)

/-- The invariant on `lv_tag`. -/
def TagOk : Obj → Prop
  | .int v s => s = (if v > 0 then 0 else if v = 0 then 1 else 2)
  | .other _ => True

/-- `PyLong_IsPositive`, :900-909 (`_PyLong_IsPositive`: sign bits == 0). -/
def isPositive : Obj → Py Bool
  | .int _ s => .ok (s % 4 == 0)
  | .other t => .error (.typeError s!"expected int, got {t}")

/-- `PyLong_IsNegative`, :911-920 (sign bits == `SIGN_NEGATIVE`). -/
def isNegative : Obj → Py Bool
  | .int _ s => .ok (s % 4 == 2)
  | .other t => .error (.typeError s!"expected int, got {t}")

/-- `PyLong_IsZero`, :922-931 (sign bits == `SIGN_ZERO`). -/
def isZero : Obj → Py Bool
  | .int _ s => .ok (s % 4 == 1)
  | .other t => .error (.typeError s!"expected int, got {t}")

/-- `PyLong_GetSign`, :953-962, with `long_sign` (:933-944): compact and non-compact sign are
both `1 - (lv_tag & SIGN_MASK)`. Its message says "expect int", unlike the other three. -/
def getSign : Obj → Py Int
  | .int _ s => .ok (1 - ((s % 4 : Nat) : Int))
  | .other t => .error (.typeError s!"expect int, got {t}")

/-- `PyLong_GetSign` gives the sign of the value, and the three predicates agree with it, for every
int; for every other object all four raise `TypeError`. -/
def SignApiAgree : Prop :=
  ∀ o : Obj, TagOk o →
    match o with
    | .int v _ =>
      getSign o = .ok (if v > 0 then 1 else if v = 0 then 0 else -1) ∧
      isPositive o = .ok (decide (v > 0)) ∧ isNegative o = .ok (decide (v < 0)) ∧ isZero o = .ok (decide (v = 0))
    | .other _ =>
      (∃ e, getSign o = .error e ∧ e.className = "TypeError") ∧
      (∃ e, isPositive o = .error e ∧ e.className = "TypeError") ∧
      (∃ e, isNegative o = .error e ∧ e.className = "TypeError") ∧
      (∃ e, isZero o = .error e ∧ e.className = "TypeError")

theorem signApiAgree_proven : SignApiAgree := by
  intro o h
  cases o with
  | int v s =>
    simp only [TagOk] at h
    subst h
    by_cases h1 : v > 0
    · simp [getSign, isPositive, isNegative, isZero, h1]; omega
    · by_cases h2 : v = 0
      · subst h2; simp [getSign, isPositive, isNegative, isZero]
      · have h3 : v < 0 := by omega
        simp [getSign, isPositive, isNegative, isZero, h1, h2, h3]
  | other t => simp [getSign, isPositive, isNegative, isZero, PyExc.className]

end PyLean.LongObj.SignApi
