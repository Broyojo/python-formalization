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

/-- A non-int operand on either side gives `NotImplemented`, before any digit is read. -/
theorem checkBinop_other {α β : Type} (f : Long → Long → Py β) (o : α) (x : Obj α) :
    checkBinop f (.other o) x = .ok none ∧ checkBinop f x (.other o) = .ok none := by
  cases x <;> exact ⟨rfl, rfl⟩

/-- A slot wrapper returns `NotImplemented` whenever either operand is not an int. -/
def NotImplementedOn {α β : Type} (m : Obj α → Obj α → Py (Option β)) : Prop :=
  ∀ (o : α) (x : Obj α), m (.other o) x = .ok none ∧ m x (.other o) = .ok none

/-- `+ - * // % divmod >> << & | ^` at the slot: the exact result for two ints, the
documented errors (ZeroDivisionError for `//`, `%` and `divmod` by zero, ValueError for a
negative shift, OverflowError when `<<` cannot allocate its result), and `NotImplemented`
from `CHECK_BINOP` (longobject.c:1843-1847) for any other operand on either side.
Hypotheses: room in `long_alloc` for the operands and for the arithmetic results. -/
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
    (b = 0 → checkBinop longMod A B = .error (.zeroDivisionError "division by zero") ∧
      checkBinop longDiv A B = .error (.zeroDivisionError "division by zero") ∧
      checkBinop longDivmod A B = .error (.zeroDivisionError "division by zero")) ∧
    (b < 0 → checkBinop longRshift A B = .error (.valueError "negative shift count")) ∧
    (0 ≤ b → checkBinop longRshift A B = .ok (some (.ofInt (a / 2 ^ b.toNat)))) ∧
    (b < 0 → checkBinop longLshift A B = .error (.valueError "negative shift count")) ∧
    (0 ≤ b → b < 2 ^ 63 → checkBinop longLshift A B =
      if a = 0 then .ok (some (.ofInt 0))
      else if lshiftNeed a b.toNat ≤ maxLongDigits then .ok (some (.ofInt (a * 2 ^ b.toNat)))
      else .error (.overflowError "too many digits in integer")) ∧
    (a ≠ 0 → 2 ^ 63 ≤ b →
      checkBinop longLshift A B = .error (.overflowError "too many digits in integer")) ∧
    (∀ op : BitOp, ∃ r, checkBinop (longBit op) A B = .ok (some (.ofInt r)) ∧
      ∀ i, bitZ r i = op.bool (bitZ a i) (bitZ b i)) ∧
    NotImplementedOn (checkBinop longAdd : Obj α → Obj α → Py (Option Long)) ∧
    NotImplementedOn (checkBinop longSub : Obj α → Obj α → Py (Option Long)) ∧
    NotImplementedOn (checkBinop (longMul false) : Obj α → Obj α → Py (Option Long)) ∧
    NotImplementedOn (checkBinop longDiv : Obj α → Obj α → Py (Option Long)) ∧
    NotImplementedOn (checkBinop longMod : Obj α → Obj α → Py (Option Long)) ∧
    NotImplementedOn (checkBinop longDivmod : Obj α → Obj α → Py (Option (Long × Long))) ∧
    NotImplementedOn (checkBinop longRshift : Obj α → Obj α → Py (Option Long)) ∧
    NotImplementedOn (checkBinop longLshift : Obj α → Obj α → Py (Option Long)) ∧
    (∀ op : BitOp, NotImplementedOn (checkBinop (longBit op) : Obj α → Obj α → Py (Option Long)))

theorem binaryMethodsExact_proven : BinaryMethodsExact := by
  intro α a b h1 h2 h3 h4
  have hb : (b = 0) → digitCount a.natAbs + 1 ≤ maxLongDigits := fun _ => by
    simp only [Sized] at h1; omega
  have hs : digitCount a.natAbs ≤ maxLongDigits := by
    simp only [Sized] at h1; omega
  have ni : ∀ {β : Type} (f : Long → Long → Py β), NotImplementedOn (checkBinop f : Obj α → Obj α → Py (Option β)) :=
    fun f o x => checkBinop_other f o x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ni _, ni _, ni _, ni _, ni _, ni _, ni _, ni _,
    fun op => ni _⟩
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
    have e3 : lDivmod (Long.ofInt a) (Long.ofInt 0) =
        .error (.zeroDivisionError "division by zero") := by
      have hd : longDivrem (Long.ofInt a) (Long.ofInt 0) =
          .error (.zeroDivisionError "division by zero") := by
        unfold longDivrem
        rw [if_pos hz]
      unfold lDivmod
      rw [if_neg hne, if_neg (by rw [hz]; omega), hd]
    have e4 : longDiv (Long.ofInt a) (Long.ofInt 0) =
        .error (.zeroDivisionError "division by zero") := by
      unfold longDiv
      rw [if_neg hne, e3]
    refine ⟨?_, ?_, ?_⟩
    · simp only [checkBinop, e2]
    · simp only [checkBinop, e4]
    · simp only [checkBinop, longDivmod, e3]
  · intro h0
    simp only [checkBinop, longRshift_spec a b hs, if_pos h0]
  · intro h0
    simp only [checkBinop, longRshift_spec a b hs, if_neg (show ¬ b < 0 by omega)]
  · intro h0
    simp only [checkBinop, (longLshift_spec a b).1 h0]
  · intro h0 h5
    simp only [checkBinop]
    rw [longLshift_int64 a b h0 h5, longLshiftInt64_spec]
    by_cases ha : a = 0
    · rw [if_pos ha, if_pos ha]
    · rw [if_neg ha, if_neg ha]
      by_cases hs : lshiftNeed a b.toNat ≤ maxLongDigits
      · rw [if_pos hs, if_pos hs]
      · rw [if_neg hs, if_neg hs]
  · intro ha hb2
    simp only [checkBinop, (longLshift_spec a b).2.2.1 ha hb2]
  · intro op
    have ha : digitCount a.natAbs + 1 ≤ maxLongDigits := by simpa only [Sized] using h1
    have hb' : digitCount b.natAbs + 1 ≤ maxLongDigits := by simpa only [Sized] using h2
    obtain ⟨r, e, f⟩ := longBit_spec op a b ha hb'
    exact ⟨r, by simp only [checkBinop, e], f⟩

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
      viaIndex index asLongLong (.other o) = .error e) ∧
    (viaIndex index asLong (.int (.ofInt a)) =
        (if -(2 ^ 63 : Int) ≤ a ∧ a < 2 ^ 63 then .ok a
          else .error (.overflowError "Python int too large to convert to C long")) ∧
      viaIndex index (fun v => .ok (asLongAndOverflow v)) (.int (.ofInt a)) =
        .ok (if -(2 ^ 63 : Int) ≤ a ∧ a < 2 ^ 63 then (a, 0)
          else (-1, if a < 0 then -1 else 1)) ∧
      viaIndex index (fun v => .ok (asUnsignedMask v)) (.int (.ofInt a)) = .ok (a % 2 ^ 64).toNat)

theorem indexConversionsExact_proven : IndexConversionsExact := by
  intro α index o a e
  refine ⟨?_, ?_, ?_⟩
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
  · exact ⟨asLong_spec a, by simp only [viaIndex, asLongAndOverflow_spec],
      by simp only [viaIndex, asUnsignedMask_spec]⟩

/-- `PyLong_AsLongLongAndOverflow`, with its own `+` loop, agrees with
`PyLong_AsLongAndOverflow` on every object whose digits are below `2**30` (the type
invariant), and so gives `(a, 0)` inside `long long` and `(-1, sign)` outside it, for an
int and for the value of `__index__`, an arbitrary fallible function whose exception
passes through. -/
def LongLongAndOverflowExact : Prop :=
  (∀ v : Long, IsDigits v.ds → asLongLongAndOverflow v = asLongAndOverflow v) ∧
  ∀ (α : Type) (index : α → Py Long) (o : α) (a : Int) (e : PyExc),
    viaIndex index (fun v => .ok (asLongLongAndOverflow v)) (.int (.ofInt a)) =
      .ok (if -(2 ^ 63 : Int) ≤ a ∧ a < 2 ^ 63 then (a, 0) else (-1, if a < 0 then -1 else 1)) ∧
    (index o = .ok (.ofInt a) →
      viaIndex index (fun v => .ok (asLongLongAndOverflow v)) (.other o) =
        .ok (if -(2 ^ 63 : Int) ≤ a ∧ a < 2 ^ 63 then (a, 0)
          else (-1, if a < 0 then -1 else 1))) ∧
    (index o = .error e →
      viaIndex index (fun v => .ok (asLongLongAndOverflow v)) (.other o) = .error e)

theorem longLongAndOverflowExact_proven : LongLongAndOverflowExact := by
  refine ⟨asLongLongAndOverflow_eq, fun α index o a e => ⟨?_, fun h => ?_, fun h => ?_⟩⟩
  · simp only [viaIndex, asLongLongAndOverflow_eq (Long.ofInt a) (digitsOf_digits a.natAbs),
      asLongAndOverflow_spec]
  · simp only [viaIndex, h, asLongLongAndOverflow_eq (Long.ofInt a) (digitsOf_digits a.natAbs),
      asLongAndOverflow_spec]
  · simp only [viaIndex, h]

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

/-- `pylong_int_divmod` (longobject.c:4422-4457) passes an import failure and an
exception from `_pylong.int_divmod` through, rejects anything but a 2-tuple with
"tuple of length 2 is required from int_divmod()" and a 2-tuple with a non-int item with
"tuple of int is required from int_divmod()", and otherwise returns the two items. For an
arbitrary (replaced) `_pylong`. With the real `_pylong.int_divmod` it gives the floor
quotient and remainder, the `l_divmod` contract. -/
def PylongDivmodPaths : Prop :=
  ∀ (imp : Py Unit) (call : Long → Long → Py PylongDivmodRes) (v w : Long),
    (∀ e, imp = .error e → pylongIntDivmodC imp call v w = .error e) ∧
    (imp = .ok () → ∀ e, call v w = .error e → pylongIntDivmodC imp call v w = .error e) ∧
    (imp = .ok () → call v w = .ok .other → pylongIntDivmodC imp call v w =
      .error (.valueError "tuple of length 2 is required from int_divmod()")) ∧
    (imp = .ok () → ∀ items, call v w = .ok (.tuple items) → items.length ≠ 2 →
      pylongIntDivmodC imp call v w =
        .error (.valueError "tuple of length 2 is required from int_divmod()")) ∧
    (imp = .ok () → ∀ x y, call v w = .ok (.tuple [x, y]) → (x = none ∨ y = none) →
      pylongIntDivmodC imp call v w =
        .error (.valueError "tuple of int is required from int_divmod()")) ∧
    (imp = .ok () → ∀ q r, call v w = .ok (.tuple [some q, some r]) →
      pylongIntDivmodC imp call v w = .ok (q, r)) ∧
    (∀ a b : Int, b ≠ 0 →
      pylongIntDivmodC (.ok ()) pylongCallDivmod (.ofInt a) (.ofInt b) =
        .ok (.ofInt (pylongIntDivmod a b).1, .ofInt (pylongIntDivmod a b).2) ∧
      IsFloorDivmod a b (pylongIntDivmod a b).1 (pylongIntDivmod a b).2)

theorem pylongDivmodPaths_proven : PylongDivmodPaths := by
  intro imp call v w
  refine ⟨fun e h => by subst h; rfl, fun h e hc => ?_, fun h hc => ?_, fun h items hc hl => ?_,
    fun h x y hc hn => ?_, fun h q r hc => ?_, fun a b hb => ?_⟩
  · subst h; unfold pylongIntDivmodC; rw [hc]; rfl
  · subst h; unfold pylongIntDivmodC; rw [hc]; rfl
  · subst h; unfold pylongIntDivmodC; rw [hc]
    match items, hl with
    | [], _ => rfl
    | [a], _ => cases a <;> rfl
    | [_, _], hl => exact absurd rfl hl
    | a :: b :: _ :: _, _ => cases a <;> cases b <;> rfl
  · subst h; unfold pylongIntDivmodC; rw [hc]
    rcases hn with hn | hn <;> subst hn
    · rfl
    · cases x <;> rfl
  · subst h; unfold pylongIntDivmodC; rw [hc]; rfl
  · refine ⟨?_, pylongIntDivmod_floor a b hb⟩
    rw [pylongIntDivmodC_real, toInt_ofInt_eq, toInt_ofInt_eq]

def entriesBinop : List Entry := [
  { id := "longobj-binary-methods", pyFile := "Objects/longobject.c"
    pyFns := ["long_add_method", "long_sub_method", "long_mul_method", "long_div", "long_mod", "long_divmod",
      "long_rshift", "long_lshift_method", "long_and", "long_or", "long_xor", "l_mod"]
    statement := "At the number slots, two ints give the exact result and the documented errors (ZeroDivisionError for //, % and divmod by zero, ValueError for a negative shift, OverflowError when << cannot allocate), and any non-int operand on either side gives NotImplemented."
    source := "stdtypes: numeric types; CHECK_BINOP at longobject.c:1843-1847", status := .proven
    prop := ``BinaryMethodsExact, thm := some ``binaryMethodsExact_proven
    notes := "Smoke-tested on 3.15.2: int.__add__ ... int.__xor__ with a float or str operand return NotImplemented; 1 // 0, 1 % 0, divmod(1, 0) raise 'division by zero'. MemoryError is not modelled." },
  { id := "longobj-pylong-divmod-paths", pyFile := "Objects/longobject.c"
    pyFns := ["pylong_int_divmod"]
    statement := "pylong_int_divmod passes an import failure and an exception from _pylong.int_divmod through, raises ValueError for a result that is not a 2-tuple or has a non-int item, and otherwise returns the two items; with the real _pylong it gives the floor quotient and remainder."
    source := "longobject.c:4426-4448; divmod() docs", status := .proven
    prop := ``PylongDivmodPaths, thm := some ``pylongDivmodPaths_proven
    notes := "Smoke-tested on 3.15.2 by replacing _pylong.int_divmod (returning (1, 2.0), ('a', 2), (1, 2, 3), [1, 2], 5, raising KeyError) and by sys.modules['_pylong'] = None, on operands of more than 300 and 450 digits." },
  { id := "longobj-index-conversions", pyFile := "Objects/longobject.c"
    pyFns := ["PyLong_AsLongAndOverflow", "PyLong_AsLong", "PyLong_AsInt",
      "PyLong_AsUnsignedLongMask", "PyLong_AsUnsignedLongLongMask", "PyLong_AsLongLong", "unroll_digits_ulong"]
    statement := "An int converts exactly; a non-int goes through __index__, an arbitrary fallible function: its value converts exactly as an int does, and its exception passes through."
    source := "C API docs: Integer Objects", status := .proven
    prop := ``IndexConversionsExact, thm := some ``indexConversionsExact_proven },
  { id := "longobj-as-long-long-and-overflow", pyFile := "Objects/longobject.c"
    pyFns := ["PyLong_AsLongLongAndOverflow", "unroll_digits_ulong"]
    statement := "PyLong_AsLongLongAndOverflow, whose loop adds each digit where PyLong_AsLongAndOverflow ors it, agrees with that twin on every object, and gives (a, 0) inside long long and (-1, sign) outside it for an int and for the value of __index__, whose exception passes through."
    source := "the implementation disagreeing with itself (twin functions); C API docs: Integer Objects", status := .proven
    prop := ``LongLongAndOverflowExact, thm := some ``longLongAndOverflowExact_proven
    notes := "The + loop is mirrored with uint64 wraparound on both the shift and the sum; accumLoopLL_eq proves neither wraps after the overflow test." },
  { id := "longobj-require-int", pyFile := "Objects/longobject.c"
    pyFns := ["PyLong_AsSsize_t", "PyLong_AsUnsignedLong", "PyLong_AsSize_t", "PyLong_AsUnsignedLongLong",
      "unroll_digits_ulong", "unroll_digits_size_t"]
    statement := "These conversions raise TypeError for a non-int and are exact, or raise OverflowError, for an int."
    source := "longobject.c:717-720 and copies", status := .proven
    prop := ``RequireIntExact, thm := some ``requireIntExact_proven }
]

end PyLean.LongObj
