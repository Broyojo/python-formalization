import PyLean.Decimal.FixExact
import PyLean.Decimal.ContextExact

/-!
The `Decimal` methods the `Context` wrappers delegate to, stated outright: operand
conversion, the unary operators, `*`, `fma`, and the `Context` methods whose result is a
property of the operand.
-/

namespace PyLean.Decimal

open PyLean

/-! ## `_convert_other` -/

/-- `_convert_other(other, raiseit)` (_pydecimal.py:6096-6113): a Decimal is returned as is; an
int `n` becomes the exact `Decimal(n)`, sign `n < 0`, coefficient `|n|`, exponent 0, unless `|n|`
has more than 4300 digits, where `Decimal(int)`'s `str(abs(value))` raises the int/str-limit
`ValueError` (:620-624); anything else is `NotImplemented`, or `TypeError` with `raiseit`. -/
def ConvertOtherExact : Prop :=
  ∀ (raiseit : Bool),
    (∀ d : Dec, convertOther raiseit (.dec d) = .ok (some d)) ∧
    (∀ n : Int, numDigits n.natAbs ≤ maxStrDigits →
      convertOther raiseit (.int n) = .ok (some (.fin (decide (n < 0)) n.natAbs 0))) ∧
    (∀ n : Int, maxStrDigits < numDigits n.natAbs →
      convertOther raiseit (.int n) = .error (.valueError limitToStrMsg)) ∧
    convertOther false .other = .ok none ∧
    convertOther true .other = .error (.typeError unableMsg) ∧
    (∀ n : Nat, convertOther false (.tuple n) = .ok none)

theorem convertOtherExact_proven : ConvertOtherExact := by
  intro r
  refine ⟨fun d => rfl, fun n h => ?_, fun n h => ?_, rfl, rfl, fun n => rfl⟩
  · simp [convertOther, pyFromInt, strLimit, show ¬ numDigits n.natAbs > maxStrDigits by omega, bind,
      Except.bind, pure, Except.pure]
  · simp [convertOther, pyFromInt, strLimit, show numDigits n.natAbs > maxStrDigits by omega, bind,
      Except.bind]

/-- `"Unable to convert %s to Decimal" % other` is the message for every operand that is not a
Decimal or an int (_pydecimal.py:6111; `~` marks the formatted operand). -/
def ConvertOtherTypeErrorMessage : Prop :=
  ∀ x : Arg, (∀ d, x ≠ .dec d) → (∀ n, x ≠ .int n) →
    convertOther true x = .error (.typeError unableMsg)

/-- `Context().plus(())`: the empty tuple is taken as `%`'s argument tuple, and the message is
"not enough arguments for format string (got 0)". -/
theorem convertOtherTypeErrorMessage_refuted : ¬ ConvertOtherTypeErrorMessage := by
  intro h
  have hm := h (.tuple 0) (fun d hd => nomatch hd) (fun n hn => nomatch hn)
  simp only [convertOther, unableMsgOf, unableMsgTuple, ↓reduceIte] at hm
  revert hm
  decide

/-! ## Unary `+`, `-`, `abs` -/

/-- `__pos__`, `__neg__`, `__abs__` (_pydecimal.py:1137-1200), for every context with `prec ≥ 1`:
a finite non-zero operand is rounded into the context by `_fix` (`fixSpec`) with its sign, the
opposite sign, and the positive sign; a zero is the zero `_fix` makes of `+0` (of `-0` for `+` of
`-0` and `-` of `+0` under `ROUND_FLOOR`, :1144-1147, :1166-1169), `abs` always `+0`; infinities
keep, flip or drop their sign; a quiet NaN is returned quieted with its own sign by all three and
a signaling one signals InvalidOperation (`_check_nans`). -/
def UnaryExact : Prop :=
  ∀ (c : Ctx) (fl : List Signal), 1 ≤ c.prec →
    (∀ (neg : Bool) (co : Nat) (e : Int), co ≠ 0 →
      (dunderPos c (.fin neg co e)).run fl = fixSpec c neg co e fl ∧
      (dunderNeg c (.fin neg co e)).run fl = fixSpec c (!neg) co e fl ∧
      (dunderAbs c (.fin neg co e)).run fl = fixSpec c false co e fl) ∧
    (∀ (neg : Bool) (e : Int),
      (dunderPos c (.fin neg 0 e)).run fl = (fix c (.fin (neg && c.rounding == .floor) 0 e)).run fl ∧
      (dunderNeg c (.fin neg 0 e)).run fl = (fix c (.fin (!neg && c.rounding == .floor) 0 e)).run fl ∧
      (dunderAbs c (.fin neg 0 e)).run fl = (fix c (.fin false 0 e)).run fl) ∧
    (∀ neg : Bool,
      (dunderPos c (.inf neg)).run fl = .ok (.inf neg, fl) ∧
      (dunderNeg c (.inf neg)).run fl = .ok (.inf (!neg), fl) ∧
      (dunderAbs c (.inf neg)).run fl = .ok (.inf false, fl)) ∧
    (∀ (neg : Bool) (p : Nat),
      (dunderPos c (.nan neg false p)).run fl = .ok (.nan neg false (p % 10 ^ nanDigits c), fl) ∧
      (dunderNeg c (.nan neg false p)).run fl = .ok (.nan neg false (p % 10 ^ nanDigits c), fl) ∧
      (dunderAbs c (.nan neg false p)).run fl = .ok (.nan neg false (p % 10 ^ nanDigits c), fl) ∧
      (dunderPos c (.nan neg true p)).run fl =
        afterSig c .invalidOperation fl (.nan neg false (p % 10 ^ nanDigits c)) ∧
      (dunderNeg c (.nan neg true p)).run fl =
        afterSig c .invalidOperation fl (.nan neg false (p % 10 ^ nanDigits c)) ∧
      (dunderAbs c (.nan neg true p)).run fl =
        afterSig c .invalidOperation fl (.nan neg false (p % 10 ^ nanDigits c)))

theorem sNaN_run (c : Ctx) (neg : Bool) (p : Nat) (fl : List Signal) :
    (do raiseSig c .invalidOperation; (pure (fixNan c neg false p) : DM Dec)).run fl =
      afterSig c .invalidOperation fl (.nan neg false (p % 10 ^ nanDigits c)) := by
  rw [raiseSig_then, fixNan_spec]

theorem unaryExact_proven : UnaryExact := by
  intro c fl hp
  refine ⟨fun neg co e hc => ?_, fun neg e => ?_, fun neg => ?_, fun neg p => ?_⟩
  · have hz : isZero (.fin neg co e) = false := by
      cases co with
      | zero => exact absurd rfl hc
      | succ n => rfl
    refine ⟨?_, ?_, ?_⟩
    · simp only [dunderPos, isSpecial, decBool, hz, Bool.not_false, Bool.false_and, Bool.false_eq_true,
        ↓reduceIte]
      exact fixExact_fin c neg co e fl hp hc
    · simp only [dunderNeg, isSpecial, decBool, hz, Bool.not_false, Bool.false_and, Bool.false_eq_true,
        ↓reduceIte, copyNegate, negate, Dec.withSign, Dec.neg]
      exact fixExact_fin c (!neg) co e fl hp hc
    · cases neg
      · simp only [dunderAbs, Dec.neg, isSpecial, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          dunderPos, decBool, hz, Bool.not_false, Bool.false_and]
        exact fixExact_fin c false co e fl hp hc
      · simp only [dunderAbs, Dec.neg, isSpecial, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          dunderNeg, decBool, hz, Bool.not_false, Bool.false_and, copyNegate, negate, Dec.withSign]
        exact fixExact_fin c false co e fl hp hc
  · refine ⟨?_, ?_, ?_⟩
    · cases neg <;> cases hr : c.rounding <;>
        simp [dunderPos, isSpecial, decBool, isZero, hr, copyAbs, Dec.withSign] <;> rfl
    · cases neg <;> cases hr : c.rounding <;>
        simp [dunderNeg, isSpecial, decBool, isZero, hr, copyAbs, copyNegate, negate, Dec.withSign, Dec.neg] <;> rfl
    · cases neg <;> cases hr : c.rounding <;>
        simp [dunderAbs, dunderPos, dunderNeg, isSpecial, decBool, isZero, hr, copyAbs, copyNegate, negate,
          Dec.withSign, Dec.neg] <;> rfl
  · refine ⟨?_, ?_, ?_⟩
    · simp [dunderPos, isSpecial, checkNans, decBool, isZero, fix, pure_run]; rfl
    · simp [dunderNeg, isSpecial, checkNans, decBool, isZero, fix, copyNegate, negate, Dec.withSign,
        Dec.neg, pure_run]; rfl
    · cases neg
      · simp [dunderAbs, dunderPos, isSpecial, checkNans, decBool, isZero, fix, Dec.neg, pure_run]; rfl
      · simp [dunderAbs, dunderNeg, isSpecial, checkNans, decBool, isZero, fix, copyNegate, negate,
          Dec.withSign, Dec.neg, pure_run]; rfl
  · have hq := fixNan_spec c neg false p
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [dunderPos, isSpecial, checkNans, hq]; rfl
    · simp [dunderNeg, isSpecial, checkNans, hq]; rfl
    · cases neg
      · simp [dunderAbs, dunderPos, isSpecial, checkNans, hq, Dec.neg]; rfl
      · simp [dunderAbs, dunderNeg, isSpecial, checkNans, hq, Dec.neg]; rfl
    · rw [← sNaN_run]; simp [dunderPos, isSpecial, checkNans]
    · rw [← sNaN_run]; simp [dunderNeg, isSpecial, checkNans]
    · rw [← sNaN_run]
      cases neg
      · simp [dunderAbs, dunderPos, isSpecial, checkNans, Dec.neg]
      · simp [dunderAbs, dunderNeg, isSpecial, checkNans, Dec.neg]

/-! ## `*` -/

/-- `__mul__` (_pydecimal.py:1312-1366) for every context with `prec ≥ 1`: two finite non-zero
operands give the exact product rounded into the context by `_fix` (`fixSpec`, overflow and the
subnormal range included), with no other error than the int/str-limit `ValueError`, which
`int(self._int) * int(other._int)` and `str()` of the product raise exactly when an operand or the
product has more than 4300 digits (an operand of coefficient 1 skips them, :1356-1361); a zero
operand gives the zero `_fix` makes of `±0·10^(ea+eb)`; an infinity times a non-zero finite value
or an infinity is the infinity of the product's sign, and times a zero is InvalidOperation. -/
def MulExact : Prop :=
  ∀ (c : Ctx) (fl : List Signal), 1 ≤ c.prec →
    (∀ (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int), ca ≠ 0 → cb ≠ 0 →
      (ca = 1 ∨ cb = 1 ∨ (numDigits ca ≤ maxStrDigits ∧ numDigits cb ≤ maxStrDigits ∧
        numDigits (ca * cb) ≤ maxStrDigits)) →
      (mul c (.fin sa ca ea) (.fin sb cb eb)).run fl = fixSpec c (sa != sb) (ca * cb) (ea + eb) fl) ∧
    (∀ (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int), ca ≠ 0 → cb ≠ 0 →
      ca ≠ 1 → cb ≠ 1 →
      (maxStrDigits < numDigits ca ∨ maxStrDigits < numDigits cb ∨ maxStrDigits < numDigits (ca * cb)) →
      ∃ m, (mul c (.fin sa ca ea) (.fin sb cb eb)).run fl = .error (.valueError m)) ∧
    (∀ (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int), ca = 0 ∨ cb = 0 →
      (mul c (.fin sa ca ea) (.fin sb cb eb)).run fl = (fix c (.fin (sa != sb) 0 (ea + eb))).run fl) ∧
    (∀ (na sb : Bool) (cb : Nat) (eb : Int),
      (mul c (.inf na) (.fin sb cb eb)).run fl =
        (if cb = 0 then afterSig c .invalidOperation fl (.nan false false 0) else .ok (.inf (na != sb), fl)) ∧
      (mul c (.fin sb cb eb) (.inf na)).run fl =
        (if cb = 0 then afterSig c .invalidOperation fl (.nan false false 0) else .ok (.inf (sb != na), fl))) ∧
    (∀ na nb : Bool, (mul c (.inf na) (.inf nb)).run fl = .ok (.inf (na != nb), fl))

theorem liftPy_run {α β : Type} (x : Py α) (g : α → DM β) (fl : List Signal) :
    (liftPy x >>= g).run fl = (match x with
      | .ok v => (g v).run fl
      | .error e => .error e) := by
  cases x <;> rfl

theorem invalid_run (c : Ctx) (fl : List Signal) :
    (invalid c).run fl = afterSig c .invalidOperation fl (.nan false false 0) := by
  simp only [invalid]; exact raiseSig_then c .invalidOperation fl _

theorem mulExact_proven : MulExact := by
  intro c fl hp
  refine ⟨fun sa ca ea sb cb eb ha hb hl => ?_, fun sa ca ea sb cb eb ha hb h1 h2 hl => ?_,
    fun sa ca ea sb cb eb h0 => ?_, fun na sb cb eb => ?_, fun na nb => ?_⟩
  · simp only [mul, Dec.neg, mulFin, ha, hb, or_self, ↓reduceIte]
    by_cases h1 : ca = 1
    · subst h1; simp only [↓reduceIte, Nat.one_mul]; exact fixExact_fin c _ cb _ fl hp hb
    by_cases h2 : cb = 1
    · subst h2; simp only [h1, ↓reduceIte, Nat.mul_one]; exact fixExact_fin c _ ca _ fl hp ha
    rcases hl with hl | hl | ⟨l1, l2, l3⟩
    · exact absurd hl h1
    · exact absurd hl h2
    simp only [h1, h2, ↓reduceIte, liftPy_run, intLimit, strLimit, show ¬ numDigits ca > maxStrDigits by omega,
      show ¬ numDigits cb > maxStrDigits by omega, show ¬ numDigits (ca * cb) > maxStrDigits by omega]
    exact fixExact_fin c _ (ca * cb) _ fl hp (Nat.mul_ne_zero ha hb)
  · simp only [mul, Dec.neg, mulFin, ha, hb, h1, h2, or_self, ↓reduceIte, liftPy_run, intLimit, strLimit]
    by_cases g1 : numDigits ca > maxStrDigits
    · exact ⟨limitToIntMsg (numDigits ca), by simp [g1]⟩
    by_cases g2 : numDigits cb > maxStrDigits
    · exact ⟨limitToIntMsg (numDigits cb), by simp [g1, g2]⟩
    have g3 : numDigits (ca * cb) > maxStrDigits := by omega
    exact ⟨limitToStrMsg, by simp [g1, g2, g3]⟩
  · simp only [mul, Dec.neg, mulFin, h0, ↓reduceIte]
  · have hz : ∀ s e, isZero (.fin s cb e) = decide (cb = 0) := by
      intro s e; cases cb <;> rfl
    refine ⟨?_, ?_⟩
    · by_cases h : cb = 0
      · simp only [mul, Dec.neg, checkNans, hz, h, decide_true, ↓reduceIte, pure_bind, bind_pure_comp]
        exact invalid_run c fl
      · simp [mul, Dec.neg, checkNans, hz, h, pure_run]; rfl
    · by_cases h : cb = 0
      · simp only [mul, Dec.neg, checkNans, hz, h, decide_true, ↓reduceIte, pure_bind, bind_pure_comp]
        exact invalid_run c fl
      · simp [mul, Dec.neg, checkNans, hz, h, pure_run]; rfl
  · simp [mul, Dec.neg, checkNans]; rfl

/-! ## `same_quantum`, `logb`, `scaleb` -/

/-- `same_quantum` (_pydecimal.py:2661-2674): two finite values have the same quantum exactly when
their exponents are equal; two NaNs and two infinities have the same quantum; a finite value never
shares a quantum with a special one, nor an infinity with a NaN. -/
def SameQuantumExact : Prop :=
  (∀ (n1 n2 : Bool) (c1 c2 : Nat) (e1 e2 : Int),
    sameQuantum (.fin n1 c1 e1) (.fin n2 c2 e2) = decide (e1 = e2)) ∧
  (∀ (a b : Dec), (isSpecial a || isSpecial b) = true →
    sameQuantum a b = ((nanKind a ≠ 0 && nanKind b ≠ 0) || (isInfinite a && isInfinite b)))

theorem sameQuantumExact_proven : SameQuantumExact := by
  refine ⟨fun n1 n2 c1 c2 e1 e2 => by simp [sameQuantum]; rfl, fun a b h => ?_⟩
  rcases a with ⟨_, _, _⟩ | _ | ⟨_, s1, _⟩ <;> rcases b with ⟨_, _, _⟩ | _ | ⟨_, s2, _⟩ <;>
    (try cases s1) <;> (try cases s2) <;>
    simp_all [sameQuantum, isSpecial, isNanP, isnan, nanKind, isInfinite, isinfinity] <;>
    (try split) <;> simp_all

/-- `logb` (_pydecimal.py:3388-3416): for a finite non-zero operand, the adjusted exponent
`A = e + digits - 1` (the exponent of its most significant digit) made into a Decimal by
`Decimal(self.adjusted())` (:3415) and rounded into the context by `_fix`; `Decimal(int)` takes
`str(abs(A))` (:621), so an `A` of more than 4300 digits raises the int/str-limit `ValueError`
instead. `logb(0)` signals DivisionByZero and gives `-Infinity`; an infinity gives `Infinity`; a NaN
goes through `_check_nans`. -/
def LogbExact : Prop :=
  ∀ (c : Ctx) (fl : List Signal), 1 ≤ c.prec →
    (∀ (neg : Bool) (co : Nat) (e : Int), co ≠ 0 → e + numDigits co - 1 ≠ 0 →
      numDigits (e + numDigits co - 1).natAbs ≤ maxStrDigits →
      (logb c (.fin neg co e)).run fl =
        fixSpec c (decide (e + numDigits co - 1 < 0)) (e + numDigits co - 1).natAbs 0 fl) ∧
    (∀ (neg : Bool) (co : Nat) (e : Int), co ≠ 0 →
      maxStrDigits < numDigits (e + numDigits co - 1).natAbs →
      (logb c (.fin neg co e)).run fl = .error (.valueError limitToStrMsg)) ∧
    (∀ (neg : Bool) (co : Nat) (e : Int), co ≠ 0 → e + numDigits co - 1 = 0 →
      (logb c (.fin neg co e)).run fl = (fix c (.fin false 0 0)).run fl) ∧
    (∀ (neg : Bool) (e : Int), (logb c (.fin neg 0 e)).run fl = afterSig c .divisionByZero fl (.inf true)) ∧
    (∀ neg : Bool, (logb c (.inf neg)).run fl = .ok (.inf false, fl)) ∧
    (∀ (neg : Bool) (p : Nat),
      (logb c (.nan neg false p)).run fl = .ok (.nan neg false (p % 10 ^ nanDigits c), fl) ∧
      (logb c (.nan neg true p)).run fl = afterSig c .invalidOperation fl (.nan neg false (p % 10 ^ nanDigits c)))

theorem logbExact_proven : LogbExact := by
  intro c fl hp
  have hz : ∀ (neg : Bool) (co : Nat) (e : Int), co ≠ 0 → decBool (.fin neg co e) = true := by
    intro neg co e hc; cases co with
    | zero => exact absurd rfl hc
    | succ n => rfl
  refine ⟨fun neg co e hc ha hl => ?_, fun neg co e hc hl => ?_, fun neg co e hc ha => ?_,
    fun neg e => ?_, fun neg => ?_, fun neg p => ?_⟩
  · simp only [logb, checkNans, isinfinity, hz neg co e hc, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, Dec.adjusted, adjustedD, pure_bind, ne_eq, not_true_eq_false, liftPy_run,
      pyFromInt, strLimit, show ¬ numDigits (e + numDigits co - 1).natAbs > maxStrDigits by omega]
    exact fixExact_fin c _ _ 0 fl hp (by omega)
  · simp only [logb, checkNans, isinfinity, hz neg co e hc, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, Dec.adjusted, adjustedD, pure_bind, ne_eq, not_true_eq_false, liftPy_run,
      pyFromInt, strLimit, show numDigits (e + numDigits co - 1).natAbs > maxStrDigits by omega]
    rfl
  · simp only [logb, checkNans, isinfinity, hz neg co e hc, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, Dec.adjusted, adjustedD, pure_bind, ne_eq, not_true_eq_false, liftPy_run,
      pyFromInt, strLimit]
    simp only [ha]; rfl
  · simp only [logb, checkNans, isinfinity, decBool, isZero, Bool.not_true, Bool.not_false,
      ↓reduceIte, pure_bind, ne_eq, not_true_eq_false]
    exact raiseSig_then c .divisionByZero fl _
  · simp [logb, checkNans, isinfinity]; cases neg <;> rfl
  · refine ⟨?_, ?_⟩
    · simp [logb, checkNans, fixNan_spec]; rfl
    · rw [← sNaN_run]; simp [logb, checkNans]

/-- `scaleb` (_pydecimal.py:3746-3769): for a finite operand `±co·10^e` and an integral second
operand `n` (exponent 0, at most 4300 digits) with `|n| ≤ 2·(Emax + prec)`, the value
`±co·10^(e+n)` rounded into the context by `_fix`; a second operand out of that range, or not
integral (a non-zero exponent, an infinity), signals InvalidOperation; an infinite first operand is
returned unchanged for an integral `n` in range; NaNs go through `_check_nans`. -/
def ScalebExact : Prop :=
  ∀ (c : Ctx) (fl : List Signal), 1 ≤ c.prec →
    (∀ (neg : Bool) (co : Nat) (e : Int) (bn : Bool) (bc : Nat),
      numDigits bc ≤ maxStrDigits →
      let n : Int := if bn then -(bc : Int) else bc
      (-(2 * (c.emax + c.prec)) ≤ n ∧ n ≤ 2 * (c.emax + c.prec) →
        (scaleb c (.fin neg co e) (.fin bn bc 0)).run fl = (fix c (.fin neg co (e + n))).run fl ∧
        (co ≠ 0 → (scaleb c (.fin neg co e) (.fin bn bc 0)).run fl = fixSpec c neg co (e + n) fl) ∧
        (scaleb c (.inf neg) (.fin bn bc 0)).run fl = .ok (.inf neg, fl)) ∧
      (¬(-(2 * (c.emax + c.prec)) ≤ n ∧ n ≤ 2 * (c.emax + c.prec)) →
        (scaleb c (.fin neg co e) (.fin bn bc 0)).run fl = afterSig c .invalidOperation fl (.nan false false 0))) ∧
    (∀ (a : Dec) (bn : Bool) (bc : Nat) (be : Int), nanKind a = 0 → be ≠ 0 →
      (scaleb c a (.fin bn bc be)).run fl = afterSig c .invalidOperation fl (.nan false false 0)) ∧
    (∀ (a : Dec) (bn : Bool), nanKind a = 0 →
      (scaleb c a (.inf bn)).run fl = afterSig c .invalidOperation fl (.nan false false 0))

theorem checkNans_none_bind (c : Ctx) (a b : Dec) (ha : nanKind a = 0) (hb : nanKind b = 0) {β : Type}
    (k : Option Dec → DM β) (fl : List Signal) :
    (checkNans c a (some b) >>= k).run fl = (k none).run fl := by
  rw [bind_run, checkNans_none c a b ha hb fl]

/-- The operand checks `rotate`, `shift` and `scaleb` share, for an integral second operand. -/
theorem intArg_run {β : Type} (c : Ctx) (a : Dec) (bn : Bool) (bc : Nat) (lo hi : Int)
    (k : Dec ⊕ Int → DM β) (fl : List Signal) (ha : nanKind a = 0) (hl : numDigits bc ≤ maxStrDigits) :
    (intArg c a (.fin bn bc 0) lo hi >>= k).run fl =
      if ¬(lo ≤ (if bn then -(bc : Int) else bc) ∧ (if bn then -(bc : Int) else bc) ≤ hi) then
        (invalid c >>= fun r => k (.inl r)).run fl
      else if isinfinity a ≠ 0 then (k (.inl a)).run fl
      else (k (.inr (if bn then -(bc : Int) else bc))).run fl := by
  simp only [intArg, bind_assoc]
  rw [checkNans_none_bind c a _ ha rfl]
  simp only [liftPy_run, intLimit, show ¬ numDigits bc > maxStrDigits by omega, ↓reduceIte, bind_assoc]
  by_cases h1 : ¬(lo ≤ (if bn then -(bc : Int) else bc) ∧ (if bn then -(bc : Int) else bc) ≤ hi)
  · simp only [h1, not_false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
  · have h1' := Decidable.of_not_not h1
    simp only [h1', and_self, not_true_eq_false, ↓reduceIte]
    by_cases h2 : isinfinity a ≠ 0
    · simp only [h2, ↓reduceIte, pure_bind, ne_eq, not_false_eq_true]
    · simp only [h2, ↓reduceIte, pure_bind, ne_eq, not_false_eq_true]

/-- A second operand that is not integral (a non-zero exponent, an infinity) is InvalidOperation. -/
theorem intArg_bad {β : Type} (c : Ctx) (a b : Dec) (lo hi : Int) (k : Dec ⊕ Int → DM β)
    (fl : List Signal) (ha : nanKind a = 0) (hb : nanKind b = 0) (h : ∀ bn bc, b ≠ .fin bn bc 0) :
    (intArg c a b lo hi >>= k).run fl = (invalid c >>= fun r => k (.inl r)).run fl := by
  simp only [intArg, bind_assoc]
  rw [checkNans_none_bind c a b ha hb]
  rcases b with ⟨bn, bc, be⟩ | bn | ⟨bn, s, p⟩
  · rcases be with ⟨_ | k⟩ | k
    · exact absurd rfl (h bn bc)
    · simp only [bind_assoc, pure_bind]
    · simp only [bind_assoc, pure_bind]
  · simp only [bind_assoc, pure_bind]
  · cases s <;> simp [nanKind] at hb

theorem scalebExact_proven : ScalebExact := by
  intro c fl hp
  have hrun : ∀ a b, (scaleb c a b).run fl = (intArg c a b (-(2 * (c.emax + c.prec))) (2 * (c.emax + c.prec)) >>=
      fun x => match x with
        | .inl r => pure r
        | .inr n => match a with
          | .fin neg co e => fix c (.fin neg co (e + n))
          | d => pure d).run fl := fun a b => rfl
  refine ⟨fun neg co e bn bc hl => ⟨fun hr => ?_, fun hr => ?_⟩, fun a bn bc be ha hb => ?_,
    fun a bn ha => ?_⟩
  · refine ⟨?_, fun hc => ?_, ?_⟩
    · rw [hrun, intArg_run c _ bn bc _ _ _ fl rfl hl]
      simp only [hr, and_self, not_true_eq_false, ↓reduceIte, isinfinity, ne_eq]
    · rw [hrun, intArg_run c _ bn bc _ _ _ fl rfl hl]
      simp only [hr, and_self, not_true_eq_false, ↓reduceIte, isinfinity, ne_eq]
      exact fixExact_fin c neg co _ fl hp hc
    · rw [hrun, intArg_run c _ bn bc _ _ _ fl rfl hl]
      simp only [hr, and_self, not_true_eq_false, ↓reduceIte, isinfinity]
      cases neg <;> rfl
  · rw [hrun, intArg_run c _ bn bc _ _ _ fl rfl hl]
    simp only [hr, not_false_eq_true, ↓reduceIte]
    rw [bind_pure]; exact invalid_run c fl
  · rw [hrun, intArg_bad c a _ _ _ _ fl ha rfl (fun bn' bc' h => by cases h; exact hb rfl)]
    rw [bind_pure]; exact invalid_run c fl
  · rw [hrun, intArg_bad c a _ _ _ _ fl ha rfl (by intro bn' bc' h; cases h)]
    rw [bind_pure]; exact invalid_run c fl

/-! ## `fma` -/

/-- `Decimal.fma` and `Context.fma` (_pydecimal.py:1975-2017, :4546-4567): the operands are
converted in order (`a`, then `b`, then `t`) and the first conversion that fails raises its error;
for finite `a`, `b` the result is `__add__` of the exact product `±(ca·cb)·10^(ea+eb)` and `t`, so
the product is not rounded ("no rounding of the intermediate product"), except for the int/str-limit
`ValueError` when a coefficient or the product has more than 4300 digits; a signaling NaN `a`, else
`b`, signals InvalidOperation and is returned quieted; an infinity times zero is InvalidOperation,
an infinity times anything else non-NaN adds the signed infinity to `t`. -/
def FmaExact : Prop :=
  (∀ (c : Ctx) (a b t : Arg) (fl : List Signal),
    match convertRaise a, convertRaise b, convertRaise t with
    | .ok x, .ok y, .ok z => (contextFma c a b t).run fl = (fma c x y z).run fl
    | .ok _, .ok _, .error e => (contextFma c a b t).run fl = .error e
    | .ok _, .error e, _ => (contextFma c a b t).run fl = .error e
    | .error e, _, _ => (contextFma c a b t).run fl = .error e) ∧
  (∀ (c : Ctx) (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int) (t : Dec) (fl : List Signal),
    numDigits ca ≤ maxStrDigits → numDigits cb ≤ maxStrDigits → numDigits (ca * cb) ≤ maxStrDigits →
    (fma c (.fin sa ca ea) (.fin sb cb eb) t).run fl = (add c (.fin (sa != sb) (ca * cb) (ea + eb)) t).run fl) ∧
  (∀ (c : Ctx) (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int) (t : Dec) (fl : List Signal),
    (maxStrDigits < numDigits ca ∨ maxStrDigits < numDigits cb ∨ maxStrDigits < numDigits (ca * cb)) →
    ∃ m, (fma c (.fin sa ca ea) (.fin sb cb eb) t).run fl = .error (.valueError m)) ∧
  (∀ (c : Ctx) (n : Bool) (p : Nat) (b t : Dec) (fl : List Signal),
    (fma c (.nan n true p) b t).run fl = afterSig c .invalidOperation fl (.nan n false (p % 10 ^ nanDigits c))) ∧
  (∀ (c : Ctx) (a : Dec) (n : Bool) (p : Nat) (t : Dec) (fl : List Signal), isSnan a = false →
    (fma c a (.nan n true p) t).run fl = afterSig c .invalidOperation fl (.nan n false (p % 10 ^ nanDigits c))) ∧
  (∀ (c : Ctx) (na sb : Bool) (eb : Int) (t : Dec) (fl : List Signal),
    (fma c (.inf na) (.fin sb 0 eb) t).run fl = afterSig c .invalidOperation fl (.nan false false 0) ∧
    (fma c (.fin sb 0 eb) (.inf na) t).run fl = afterSig c .invalidOperation fl (.nan false false 0)) ∧
  (∀ (c : Ctx) (na sb : Bool) (cb : Nat) (eb : Int) (t : Dec) (fl : List Signal), cb ≠ 0 →
    (fma c (.inf na) (.fin sb cb eb) t).run fl = (add c (.inf (na != sb)) t).run fl ∧
    (fma c (.fin sb cb eb) (.inf na) t).run fl = (add c (.inf (sb != na)) t).run fl)

theorem fmaExact_proven : FmaExact := by
  refine ⟨fun c a b t fl => ?_, fun c sa ca ea sb cb eb t fl h1 h2 h3 => ?_,
    fun c sa ca ea sb cb eb t fl hl => ?_, fun c n p b t fl => ?_, fun c a n p t fl ha => ?_,
    fun c na sb eb t fl => ?_, fun c na sb cb eb t fl hc => ?_⟩
  · cases ha : convertRaise a with
    | error e => simp only [contextFma]; exact liftPy_err_run _ fl ha
    | ok x =>
      cases hb : convertRaise b with
      | error e => simp only [contextFma]; rw [liftPy_ok_run _ fl ha]; exact liftPy_err_run _ fl hb
      | ok y =>
        cases ht : convertRaise t with
        | error e =>
          simp only [contextFma]; rw [liftPy_ok_run _ fl ha, liftPy_ok_run _ fl hb]
          exact liftPy_err_run _ fl ht
        | ok z => exact contextFma_equiv c a b t x y z fl ha hb ht
  · simp only [fma, liftPy_run, intLimit, strLimit, show ¬ numDigits ca > maxStrDigits by omega,
      show ¬ numDigits cb > maxStrDigits by omega, show ¬ numDigits (ca * cb) > maxStrDigits by omega,
      ↓reduceIte]
  · simp only [fma, liftPy_run, intLimit, strLimit]
    by_cases g1 : numDigits ca > maxStrDigits
    · exact ⟨limitToIntMsg (numDigits ca), by simp [g1]⟩
    by_cases g2 : numDigits cb > maxStrDigits
    · exact ⟨limitToIntMsg (numDigits cb), by simp [g1, g2]⟩
    have g3 : numDigits (ca * cb) > maxStrDigits := by omega
    exact ⟨limitToStrMsg, by simp [g1, g2, g3]⟩
  · rw [← sNaN_run]
    cases b <;> simp [fma, isSnan, isnan, nanKind, quietOf]
  · have hq : quietOf c (.nan n true p) = fixNan c n false p := rfl
    rw [← sNaN_run]
    rcases a with ⟨_, _, _⟩ | _ | ⟨_, s, _⟩
    · simp [fma, isSnan, isnan, nanKind, quietOf]
    · simp [fma, isSnan, isnan, nanKind, quietOf]
    · cases s
      · simp [fma, isSnan, isnan, nanKind, quietOf]
      · simp [isSnan, isnan, nanKind] at ha
  · refine ⟨?_, ?_⟩
    · simp only [fma, isSnan, isnan, nanKind, isQnan, isinfinity, decBool, isZero]
      cases na <;> simp <;> exact invalid_run c fl
    · simp only [fma, isSnan, isnan, nanKind, isQnan, isinfinity, decBool, isZero]
      cases na <;> simp <;> exact invalid_run c fl
  · have hz : isZero (.fin sb cb eb) = false := by
      cases cb with
      | zero => exact absurd rfl hc
      | succ n => rfl
    refine ⟨?_, ?_⟩
    · cases na <;> simp [fma, isSnan, isnan, nanKind, isQnan, isinfinity, decBool, hz, Dec.neg]
    · cases na <;> simp [fma, isSnan, isnan, nanKind, isQnan, isinfinity, decBool, hz, Dec.neg]

/-! ## `Context.is_signed`, `canonical`, `is_canonical` -/

/-- `Context.is_signed(a)` (_pydecimal.py:4673-4688) is the sign of the converted operand: a
Decimal's sign bit (`-0` is signed), `n < 0` for an int within the int/str limit; and
`Context.canonical` / `is_canonical` (:4255-4266, :4569-4580) return the Decimal itself / True for
a Decimal and raise `TypeError` for every other operand, ints included. -/
def ContextPredicatesExact : Prop :=
  (∀ (c : Ctx) (d : Dec) (fl : List Signal), (contextIsSigned c (.dec d)).run fl = .ok (d.neg, fl)) ∧
  (∀ (c : Ctx) (n : Int) (fl : List Signal), numDigits n.natAbs ≤ maxStrDigits →
    (contextIsSigned c (.int n)).run fl = .ok (decide (n < 0), fl)) ∧
  (∀ d : Dec, contextCanonical (.dec d) = .ok d ∧ contextIsCanonical (.dec d) = .ok true) ∧
  (∀ x : Arg, (∀ d, x ≠ .dec d) →
    contextCanonical x = .error (.typeError "canonical requires a Decimal as an argument.") ∧
    contextIsCanonical x = .error (.typeError "is_canonical requires a Decimal as an argument."))

theorem contextPredicatesExact_proven : ContextPredicatesExact := by
  refine ⟨fun c d fl => rfl, fun c n fl h => ?_, fun d => ⟨rfl, rfl⟩, fun x hx => ?_⟩
  · have hc := (convertOtherExact_proven true).2.1 n h
    simp only [contextIsSigned, ctxUn, convertRaise, hc]
    rfl
  · cases x with
    | dec d => exact absurd rfl (hx d)
    | _ => exact ⟨rfl, rfl⟩

end PyLean.Decimal
