import PyLean.Registry
import PyLean.LongObj.Conv2

/-!
The object-level entry points: what happens before the digit code runs.

`CHECK_BINOP`, longobject.c:1843-1847, returns `NotImplemented` unless both operands are
ints, and is the only code in the `*_method` wrappers. The `PyLong_As*` family either calls
`__index__` on a non-int, which runs arbitrary Python and may raise, or refuses it with
`TypeError`. Both are failure paths, so they are mirrored here over `Obj`, with
`__index__` an arbitrary fallible function.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt PyLean.Registry

/-- An argument: an `int` (or subclass), or any other object. -/
inductive Obj (α : Type) where
  | int (v : Long)
  | other (o : α)

/-- `CHECK_BINOP(v, w)` around a binary slot; `none` is `NotImplemented`. -/
def checkBinop {α β : Type} (f : Long → Long → Py β) : Obj α → Obj α → Py (Option β)
  | .int a, .int b =>
    match f a b with
    | .ok r => .ok (some r)
    | .error e => .error e
  | _, _ => .ok none

/-- `if (PyLong_Check(vv)) v = vv; else v = _PyNumber_Index(vv);`, longobject.c:608-616. -/
def viaIndex {α β : Type} (index : α → Py Long) (f : Long → Py β) : Obj α → Py β
  | .int v => f v
  | .other o =>
    match index o with
    | .ok v => f v
    | .error e => .error e

/-- `if (!PyLong_Check(vv)) TypeError`, longobject.c:717-720. -/
def requireInt {α β : Type} (f : Long → Py β) : Obj α → Py β
  | .int v => f v
  | .other _ => .error (.typeError "an integer is required")

/-- `+ - * // % divmod >> << & | ^` at the slot: the exact result for two ints, and
`NotImplemented` for any other operand. Hypotheses: room in `long_alloc`. -/
def BinaryMethodsExact : Prop :=
  ∀ (α : Type) (a b : Int), Sized a → Sized b →
    digitCount a.natAbs + digitCount b.natAbs + 2 ≤ maxLongDigits → DivSized a b →
    let A : Obj α := .int (.ofInt a)
    let B : Obj α := .int (.ofInt b)
    checkBinop longAdd A B = .ok (some (.ofInt (a + b))) ∧
    checkBinop longSub A B = .ok (some (.ofInt (a - b))) ∧
    checkBinop (longMul false) A B = .ok (some (.ofInt (a * b))) ∧
    (b ≠ 0 →
      (∃ q r, checkBinop longDivmod A B = .ok (some (.ofInt q, .ofInt r)) ∧ IsFloorDivmod a b q r) ∧
      (∃ q r, checkBinop longDiv A B = .ok (some (.ofInt q)) ∧ IsFloorDivmod a b q r) ∧
      (∃ q r, checkBinop longMod A B = .ok (some (.ofInt r)) ∧ IsFloorDivmod a b q r)) ∧
    (b = 0 → checkBinop longMod A B = .error (.zeroDivisionError "division by zero")) ∧
    (b < 0 → checkBinop longRshift A B = .error (.valueError "negative shift count")) ∧
    (0 ≤ b → checkBinop longRshift A B = .ok (some (.ofInt (a / 2 ^ b.toNat)))) ∧
    (b < 0 → checkBinop longLshift A B = .error (.valueError "negative shift count")) ∧
    (0 ≤ b → b < 2 ^ 63 → digitCount a.natAbs + b.toNat / 30 + 1 ≤ maxLongDigits →
      checkBinop longLshift A B = .ok (some (.ofInt (a * 2 ^ b.toNat)))) ∧
    (∀ op : BitOp, ∃ r, checkBinop (longBit op) A B = .ok (some (.ofInt r)) ∧
      ∀ i, bitZ r i = op.bool (bitZ a i) (bitZ b i))

theorem binaryMethodsExact_proven : BinaryMethodsExact := by
  intro α a b h1 h2 h3 h4
  have hb : (b = 0) → digitCount a.natAbs + 1 ≤ maxLongDigits := fun _ => by
    simp only [Sized] at h1; omega
  have hs : digitCount a.natAbs ≤ maxLongDigits := by
    simp only [Sized] at h1; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [checkBinop, longAdd_spec a b h1 h2]
  · simp only [checkBinop, longSub_spec a b h1 h2]
  · simp only [checkBinop, longMul_spec false a b (by simp) h3]
  · intro h0
    obtain ⟨q1, r1, e1, f1⟩ := lDivmod_floor a b h4 h0
    obtain ⟨q2, r2, e2, f2⟩ := longDiv_floor a b h4 h0
    obtain ⟨q3, r3, e3, f3⟩ := lMod_floor a b h4 h0
    refine ⟨⟨q1, r1, ?_, f1⟩, ⟨q2, r2, ?_, f2⟩, ⟨q3, r3, ?_, f3⟩⟩
    · simp only [checkBinop, longDivmod, e1]
    · simp only [checkBinop, e2]
    · simp only [checkBinop, longMod, e3]
  · intro h0
    subst h0
    have hz : (Long.ofInt 0).ds.length = 0 := rfl
    have hne : ¬ ((Long.ofInt a).ds.length = 1 ∧ (Long.ofInt (0 : Int)).ds.length = 1) := by
      intro h; omega
    have e1 : longRem (Long.ofInt a) (Long.ofInt 0) =
        .error (.zeroDivisionError "division by zero") := by
      unfold longRem
      rw [if_pos hz]
    have e2 : longMod (Long.ofInt a) (Long.ofInt 0) =
        .error (.zeroDivisionError "division by zero") := by
      unfold longMod lMod
      rw [if_neg hne, e1]
    simp only [checkBinop, e2]
  · intro h0
    simp only [checkBinop, longRshift_spec a b hs, if_pos h0]
  · intro h0
    simp only [checkBinop, longRshift_spec a b hs, if_neg (show ¬ b < 0 by omega)]
  · intro h0
    simp only [checkBinop, (longLshift_spec a b).1 h0]
  · intro h0 h5 h6
    simp only [checkBinop, (longLshift_spec a b).2.2.2 h0 h5 h6]
  · intro op
    have ha : digitCount a.natAbs + 1 ≤ maxLongDigits := by simpa only [Sized] using h1
    have hb' : digitCount b.natAbs + 1 ≤ maxLongDigits := by simpa only [Sized] using h2
    obtain ⟨r, e, f⟩ := longBit_spec op a b ha hb'
    exact ⟨r, by simp only [checkBinop, e], f⟩

/-- A non-int operand on either side gives `NotImplemented`, before any digit is read. -/
theorem checkBinop_other {α β : Type} (f : Long → Long → Py β) (o : α) (x : Obj α) :
    checkBinop f (.other o) x = .ok none ∧ checkBinop f x (.other o) = .ok none := by
  cases x <;> exact ⟨rfl, rfl⟩

/-- The conversions that accept `__index__`: an int converts exactly; another object takes
the value `__index__` returns, and `__index__`'s exception passes through. -/
def IndexConversionsExact : Prop :=
  ∀ (α : Type) (index : α → Py Long) (o : α) (a : Int) (e : PyExc),
    (index o = .ok (.ofInt a) →
      viaIndex index asLong (.other o) =
        (if -(2 ^ 63 : Int) ≤ a ∧ a < 2 ^ 63 then .ok a
          else .error (.overflowError "Python int too large to convert to C long")) ∧
      viaIndex index asCInt (.other o) =
        (if -(2 ^ 31 : Int) ≤ a ∧ a < 2 ^ 31 then .ok a
          else .error (.overflowError "Python int too large to convert to C int")) ∧
      viaIndex index (fun v => .ok (asLongAndOverflow v)) (.other o) =
        .ok (if -(2 ^ 63 : Int) ≤ a ∧ a < 2 ^ 63 then (a, 0)
          else (-1, if a < 0 then -1 else 1)) ∧
      viaIndex index (fun v => .ok (asUnsignedMask v)) (.other o) = .ok (a % 2 ^ 64).toNat ∧
      (-(2 ^ 63 : Int) ≤ a ∧ a < 2 ^ 63 → viaIndex index asLongLong (.other o) = .ok a) ∧
      (¬ (-(2 ^ 63 : Int) ≤ a ∧ a < 2 ^ 63) →
        (viaIndex index asLongLong (.other o)).raises "OverflowError")) ∧
    (index o = .error e →
      viaIndex index asLong (.other o) = .error e ∧
      viaIndex index asCInt (.other o) = .error e ∧
      viaIndex index asLongLong (.other o) = .error e)

theorem indexConversionsExact_proven : IndexConversionsExact := by
  intro α index o a e
  constructor
  · intro h
    have hL := asLongLong_spec a
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [viaIndex, h, asLong_spec]
    · simp only [viaIndex, h, asCInt_spec]
    · simp only [viaIndex, h, asLongAndOverflow_spec]
    · simp only [viaIndex, h, asUnsignedMask_spec]
    · intro h2
      simp only [viaIndex, h, hL.1 h2]
    · intro h2
      simp only [viaIndex, h]
      exact hL.2 h2
  · intro h
    simp only [viaIndex, h, and_self]

/-- The conversions that refuse non-ints: `TypeError`, and otherwise exact. -/
def RequireIntExact : Prop :=
  ∀ (α : Type) (o : α) (a : Int),
    (requireInt asSsize (.other o : Obj α) = .error (.typeError "an integer is required")) ∧
    (requireInt asUnsignedLong (.other o : Obj α) = .error (.typeError "an integer is required")) ∧
    (requireInt asSizeT (.other o : Obj α) = .error (.typeError "an integer is required")) ∧
    (requireInt asUnsignedLongLong (.other o : Obj α) = .error (.typeError "an integer is required")) ∧
    requireInt asSsize (.int (.ofInt a) : Obj α) =
      (if -(2 ^ 63 : Int) ≤ a ∧ a < 2 ^ 63 then .ok a
        else .error (.overflowError "Python int too large to convert to C ssize_t")) ∧
    requireInt asUnsignedLong (.int (.ofInt a) : Obj α) =
      (if a < 0 then .error (.overflowError "can't convert negative value to unsigned int")
      else if a < 2 ^ 64 then .ok a.toNat
      else .error (.overflowError "Python int too large to convert to C unsigned long")) ∧
    requireInt asSizeT (.int (.ofInt a) : Obj α) =
      (if a < 0 then .error (.overflowError "can't convert negative value to size_t")
      else if a < 2 ^ 64 then .ok a.toNat
      else .error (.overflowError "Python int too large to convert to C size_t")) ∧
    (0 ≤ a ∧ a < 2 ^ 64 → requireInt asUnsignedLongLong (.int (.ofInt a) : Obj α) = .ok a.toNat) ∧
    (¬ (0 ≤ a ∧ a < 2 ^ 64) →
      (requireInt asUnsignedLongLong (.int (.ofInt a) : Obj α)).raises "OverflowError")

theorem requireIntExact_proven : RequireIntExact := by
  intro α o a
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact asSsize_spec a
  · exact asUnsignedLong_spec a
  · exact asSizeT_spec a
  · exact (asUnsignedLongLong_spec a).1
  · exact (asUnsignedLongLong_spec a).2

def entriesBinop : List Entry := [
  { id := "longobj-binary-methods", pyFile := "Objects/longobject.c"
    pyFns := ["long_add_method", "long_sub_method", "long_mul_method", "long_div", "long_mod", "long_divmod",
      "long_rshift", "long_lshift_method", "long_and", "long_or", "long_xor"]
    statement := "At the number slots, two ints give the exact result and the documented errors, for all operands with room in long_alloc."
    source := "stdtypes: numeric types", status := .proven
    prop := ``BinaryMethodsExact, thm := some ``binaryMethodsExact_proven
    notes := "`checkBinop_other` gives NotImplemented for any non-int operand. MemoryError is not modelled." },
  { id := "longobj-index-conversions", pyFile := "Objects/longobject.c"
    pyFns := ["PyLong_AsLongAndOverflow", "PyLong_AsLongLongAndOverflow", "PyLong_AsLong", "PyLong_AsInt",
      "PyLong_AsUnsignedLongMask", "PyLong_AsUnsignedLongLongMask", "PyLong_AsLongLong", "unroll_digits_ulong"]
    statement := "A non-int goes through __index__, an arbitrary fallible function: its value converts exactly as an int does, and its exception passes through."
    source := "C API docs: Integer Objects", status := .proven
    prop := ``IndexConversionsExact, thm := some ``indexConversionsExact_proven },
  { id := "longobj-require-int", pyFile := "Objects/longobject.c"
    pyFns := ["PyLong_AsSsize_t", "PyLong_AsUnsignedLong", "PyLong_AsSize_t", "PyLong_AsUnsignedLongLong",
      "unroll_digits_ulong", "unroll_digits_size_t"]
    statement := "These conversions raise TypeError for a non-int and are exact, or raise OverflowError, for an int."
    source := "longobject.c:717-720 and copies", status := .proven
    prop := ``RequireIntExact, thm := some ``requireIntExact_proven }
]

end PyLean.LongObj
