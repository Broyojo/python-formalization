import PyLean.MathInt.Round
import PyLean.LongObj.Binop

/-!
`_PyLong_DivmodNear` and `int.__round__`, `Objects/longobject.c:6112-6265` (CPython
3.15.2), at the object level: the argument checks, `long_divrem`'s ZeroDivisionError
and `_PyNumber_Index` on `ndigits`, around the value-level fix-up `MathInt.divmodNear`
(which follows :6146-6185) and `MathInt.roundInt`.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt PyLean.Registry

/-- `_PyLong_DivmodNear(a, b)`, longobject.c:6117-6193: the TypeError of :6140-6144 unless
both are ints, then `long_divrem` (:6149-6150), whose only failure here is
ZeroDivisionError, then the round-half-to-even fix-up. -/
def divmodNearObj {α : Type} (a b : Obj α) : Py (Long × Long) :=
  match a, b with
  | .int a, .int b =>
    match longDivrem a b with
    | .error e => .error e
    | .ok _ =>
      let p := divmodNear a.toInt b.toInt
      .ok (Long.ofInt p.1, Long.ofInt p.2)
  | _, _ => .error (.typeError "non-integer arguments in division")

/-- `int.__round__(self, ndigits)`, longobject.c:6206-6265. `none` is `ndigits` omitted or
`None` (:6224-6225); otherwise `_PyNumber_Index(o_ndigits)` (:6227-6229): an int is
used as it is, and any other object goes through `index`, its `__index__` (or the
TypeError for an object without one), which can raise. -/
def intRound {α : Type} (index : α → Py Long) (self : Int) : Option (Obj α) → Py Int
  | none => .ok self
  | some x =>
    match viaIndex index (fun v => .ok v) x with
    | .error e => .error e
    | .ok nd => .ok (roundInt self (some nd.toInt))

/-- `divmodNear` with a negative divisor is the positive case on `(-a, -b)` with the
remainder negated. -/
theorem divmodNear_spec_neg (a b : Int) (hb : b < 0) :
    a = (divmodNear a b).1 * b + (divmodNear a b).2 ∧
    2 * (divmodNear a b).2.natAbs ≤ b.natAbs ∧
    (2 * (divmodNear a b).2.natAbs = b.natAbs → (divmodNear a b).1 % 2 = 0) := by
  obtain ⟨B, hBdef⟩ : ∃ B : Nat, b = -(B : Int) := ⟨b.natAbs, by omega⟩
  subst hBdef
  have hB0 : 0 < B := by omega
  have nb : -(B : Int) < 0 := by omega
  obtain ⟨A, hA | hA⟩ := natAbs_cases a <;> subst hA
  all_goals
    have e1 := Nat.div_add_mod A B
    have m1 := Nat.mod_lt A hB0
    unfold divmodNear
    simp only [Int.tdiv_neg, Int.tmod_neg, Int.neg_tdiv, Int.neg_tmod, ← Int.ofNat_tdiv,
      ← Int.ofNat_tmod, nb, decide_true, Int.natAbs_neg, Int.natAbs_natCast, ite_true,
      Int.neg_neg]
    generalize A / B = Q at *
    generalize A % B = R at *
  · -- a = A ≥ 0: the quotient is negative
    have hd : decide ((A : Int) < 0) = false := by simp
    simp only [hd, ne_eq, Bool.false_eq_true, not_false_eq_true, ite_true]
    by_cases hc : -(2 * (R : Int)) < -(B : Int) ∨ (-(2 * (R : Int)) = -(B : Int) ∧ Q % 2 = 1)
    · rw [if_pos hc]
      refine ⟨by grind, ?_, ?_⟩ <;> omega
    · rw [if_neg hc]
      refine ⟨by grind, ?_, ?_⟩ <;> omega
  · -- a = -A
    by_cases hA0 : A = 0
    · subst hA0
      have hR : R = 0 := by omega
      have hQ : B * Q = 0 := by omega
      have hQ0 : Q = 0 := by rcases Nat.mul_eq_zero.mp hQ with h | h <;> omega
      subst hR hQ0
      have hBn : ¬ ((B : Int) < 0) := by omega
      simp [hBn]
    have hd : decide (-(A : Int) < 0) = true := by simp; omega
    simp only [hd, ne_eq, not_true_eq_false, ite_false]
    split <;> refine ⟨by grind, ?_, ?_⟩ <;> omega

/-- `_PyLong_DivmodNear(a, b)` raises "non-integer arguments in division" unless both
arguments are ints, ZeroDivisionError for `b == 0`, and otherwise returns `(q, r)` with
`a == q*b + r`, `2*abs(r) <= abs(b)`, and `q` even on a tie (the comment at :6112-6115),
for every sign of `a` and `b`; `datetime` passes negative divisors. The room for
`long_divrem`'s work copy is an allocation bound. -/
def DivmodNearExact : Prop :=
  ∀ (α : Type) (o : α) (x : Obj α) (a b : Int),
    divmodNearObj (.other o) x = .error (.typeError "non-integer arguments in division") ∧
    divmodNearObj x (.other o) = .error (.typeError "non-integer arguments in division") ∧
    divmodNearObj (.int (.ofInt a) : Obj α) (.int (.ofInt 0)) =
      .error (.zeroDivisionError "division by zero") ∧
    (b ≠ 0 → digitCount a.natAbs + 1 ≤ maxLongDigits →
      ∃ q r, divmodNearObj (.int (.ofInt a) : Obj α) (.int (.ofInt b)) = .ok (.ofInt q, .ofInt r) ∧
        a = q * b + r ∧ 2 * r.natAbs ≤ b.natAbs ∧ (2 * r.natAbs = b.natAbs → q % 2 = 0))

theorem divmodNearExact_proven : DivmodNearExact := by
  intro α o x a b
  refine ⟨by cases x <;> rfl, by cases x <;> rfl, ?_, fun hb hs => ?_⟩
  · have hz : (Long.ofInt 0).ds.length = 0 := rfl
    simp only [divmodNearObj, longDivrem, hz, ite_true]
  · refine ⟨(divmodNear a b).1, (divmodNear a b).2, ?_, ?_⟩
    · simp only [divmodNearObj, longDivrem_spec a b hb hs, Long.toInt_ofInt]
    · rcases Int.lt_or_gt_of_ne hb with h | h
      · exact divmodNear_spec_neg a b h
      · obtain ⟨h1, h2, h3⟩ := divmodNear_spec a b h
        refine ⟨h1, by omega, fun ht => h3 (by omega)⟩

/-- `round(x, ndigits)` for an int: `x` for `None`; `ndigits` goes through
`_PyNumber_Index`, so an int is used directly, another object's `__index__` (an arbitrary
fallible function) supplies the value, and its exception (or the TypeError of an object
without `__index__`) passes through; then the documented rounding, stated by
`RoundIntHalfEven`, which this conjunction includes. -/
def IntRoundExact : Prop :=
  RoundIntHalfEven ∧
  ∀ (α : Type) (index : α → Py Long) (self : Int),
    intRound index self none = .ok self ∧
    (∀ nd : Int, intRound index self (some (.int (.ofInt nd))) = .ok (roundInt self (some nd))) ∧
    (∀ (o : α) (nd : Int), index o = .ok (.ofInt nd) →
      intRound index self (some (.other o)) = .ok (roundInt self (some nd))) ∧
    (∀ (o : α) (e : PyExc), index o = .error e → intRound index self (some (.other o)) = .error e)

theorem intRoundExact_proven : IntRoundExact := by
  refine ⟨roundIntHalfEven_proven, fun α index self => ⟨rfl, fun nd => ?_, fun o nd h => ?_,
    fun o e h => ?_⟩⟩
  · simp [intRound, viaIndex, Long.toInt_ofInt]
  · simp [intRound, viaIndex, h, Long.toInt_ofInt]
  · simp [intRound, viaIndex, h]

end PyLean.LongObj
