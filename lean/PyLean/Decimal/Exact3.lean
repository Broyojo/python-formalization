import PyLean.Decimal.DelegateExact2
import PyLean.Decimal.ExactProps

/-!
The branches the earlier exact statements left out: NaN operands of `*`, `normalize`, `scaleb`
and `fma`; `scaleb`'s int/str limit and an infinite first operand out of range; the special products
of `fma`, added to the third operand; `abs(round=False)`; `compare_total_mag` with a NaN second
operand; `_convert_other` of a tuple with `raiseit`.
-/

namespace PyLean.Decimal

open PyLean

/-! ## `_check_nans(self, other)` then `if ans: return ans` -/

/-- What a binary operation that starts with `ans = self._check_nans(other, context); if ans:
return ans` (_pydecimal.py:790-820) gives when an operand is a NaN: a signaling NaN on the left,
else on the right, signals InvalidOperation (raising if trapped) and is returned quiet with its
payload cut to `prec - clamp` digits; otherwise the left quiet NaN, else the right one, is returned
so, with no flag. -/
def nanSpec2 (c : Ctx) (a b : Dec) (fl : List Signal) : Py (Dec × List Signal) :=
  if nanKind a = 2 then afterSig c .invalidOperation fl (quietNaN c a)
  else if nanKind b = 2 then afterSig c .invalidOperation fl (quietNaN c b)
  else if nanKind a = 1 then .ok (quietNaN c a, fl)
  else .ok (quietNaN c b, fl)

theorem checkNans_return (c : Ctx) (a b : Dec) (fl : List Signal) (k : Option Dec → DM Dec)
    (hk : ∀ d, k (some d) = pure d) (h : nanKind a ≠ 0 ∨ nanKind b ≠ 0) :
    (checkNans c a (some b) >>= k).run fl = nanSpec2 c a b fl := by
  have sig : ∀ x, ((do raiseSig c .invalidOperation; (pure (some x) : DM (Option Dec))) >>= k).run fl =
      afterSig c .invalidOperation fl x := by
    intro x; rw [bind_assoc]; simp only [pure_bind, hk]; exact raiseSig_then c _ fl x
  have ok : ∀ x, ((pure (some x) : DM (Option Dec)) >>= k).run fl = .ok (x, fl) := by
    intro x; rw [pure_bind, hk]; rfl
  rcases a with ⟨na, ca, ea⟩ | na | ⟨na, sa, pa⟩ <;> rcases b with ⟨nb, cb, eb⟩ | nb | ⟨nb, sb, pb⟩ <;>
    (try cases sa) <;> (try cases sb) <;>
    first
    | (simp [nanKind] at h; done)
    | (simp only [checkNans]
       first
       | (rw [sig]; simp [nanSpec2, nanKind, quietNaN, fixNan_spec])
       | (rw [ok]; simp [nanSpec2, nanKind, quietNaN, fixNan_spec]))

/-! ## `*` with a NaN, and the operator prologue -/

/-- `__mul__` (_pydecimal.py:1312-1366) with a NaN operand: `_check_nans` (:1326-1329) decides the
result, `nanSpec2`, whatever the other operand is (an infinity included: no InvalidOperation for
`NaN * Infinity` beyond a signaling NaN's). And the prologue `other = _convert_other(other); if other
is NotImplemented: return other` (:1317-1319): a Decimal operand is multiplied as is, an int `n` as
the exact `Decimal(n)` (the int/str-limit `ValueError` when `|n|` has more than 4300 digits), and any
other operand gives `NotImplemented` (`none`) with no flag. -/
def MulNanExact : Prop :=
  (∀ (c : Ctx) (a b : Dec) (fl : List Signal), nanKind a ≠ 0 ∨ nanKind b ≠ 0 →
    (mul c a b).run fl = nanSpec2 c a b fl) ∧
  (∀ (c : Ctx) (a d : Dec) (fl : List Signal),
    (opArg mul c a (.dec d)).run fl = (fun p => (some p.1, p.2)) <$> (mul c a d).run fl) ∧
  (∀ (c : Ctx) (a : Dec) (n : Int) (fl : List Signal), numDigits n.natAbs ≤ maxStrDigits →
    (opArg mul c a (.int n)).run fl =
      (fun p => (some p.1, p.2)) <$> (mul c a (.fin (decide (n < 0)) n.natAbs 0)).run fl) ∧
  (∀ (c : Ctx) (a : Dec) (n : Int) (fl : List Signal), maxStrDigits < numDigits n.natAbs →
    (opArg mul c a (.int n)).run fl = .error (.valueError limitToStrMsg)) ∧
  (∀ (c : Ctx) (a : Dec) (fl : List Signal),
    (∀ s, (opArg mul c a (.other s)).run fl = .ok (none, fl)) ∧ ∀ t, (opArg mul c a (.tuple t)).run fl = .ok (none, fl))

theorem opArg_dec {α : Type} (f : Ctx → Dec → Dec → DM α) (c : Ctx) (a d : Dec) (fl : List Signal) :
    (opArg f c a (.dec d)).run fl = (fun p => (some p.1, p.2)) <$> (f c a d).run fl := by
  simp only [opArg, convertOther, liftPy_run]
  simp only [StateT.run, bind, StateT.bind, pure, StateT.pure, Functor.map, Except.map]
  cases f c a d fl <;> rfl

theorem mulNanExact_proven : MulNanExact := by
  refine ⟨fun c a b fl h => ?_, fun c a d fl => opArg_dec mul c a d fl, fun c a n fl hl => ?_,
    fun c a n fl hl => ?_, fun c a fl => ⟨fun _ => rfl, fun _ => rfl⟩⟩
  · rcases a with ⟨_, _, _⟩ | _ | ⟨_, sa, _⟩ <;> rcases b with ⟨_, _, _⟩ | _ | ⟨_, sb, _⟩ <;>
      first
      | (simp [nanKind] at h; done)
      | (simp only [mul]; exact checkNans_return c _ _ fl _ (fun d => rfl) h)
  · have hc := (convertOtherExact_proven false).2.1 n hl
    simp only [opArg, hc, liftPy_run]
    simp only [StateT.run, bind, StateT.bind, pure, StateT.pure, Functor.map, Except.map]
    cases mul c a (.fin (decide (n < 0)) n.natAbs 0) fl <;> rfl
  · have hc := (convertOtherExact_proven false).2.2.1 n hl
    simp only [opArg, hc, liftPy_run]

/-! ## `normalize` of a NaN -/

/-- `normalize` (_pydecimal.py:2575-2598) of a NaN: `_check_nans` (:2581-2584) returns a quiet NaN
quieted (its payload cut to `prec - clamp` digits) with no flag, and a signaling NaN signals
InvalidOperation and is returned quiet. -/
def NormalizeNanExact : Prop :=
  ∀ (c : Ctx) (fl : List Signal) (neg : Bool) (p : Nat),
    (normalize c (.nan neg false p)).run fl = .ok (.nan neg false (p % 10 ^ nanDigits c), fl) ∧
    (normalize c (.nan neg true p)).run fl = afterSig c .invalidOperation fl (.nan neg false (p % 10 ^ nanDigits c))

theorem normalizeNanExact_proven : NormalizeNanExact := by
  intro c fl neg p
  refine ⟨?_, ?_⟩
  · simp [normalize, checkNans, fixNan_spec]; rfl
  · rw [← sNaN_run]; simp [normalize, checkNans]

/-! ## `scaleb`: NaNs, the int/str limit, an infinite first operand -/

/-- `scaleb` (_pydecimal.py:3746-3769), the branches `ScalebExact` leaves: a NaN operand goes
through `_check_nans` (:3753-3755), `nanSpec2`; for an integral second operand `n` whose digit
string has more than 4300 digits, `int(other)` (:3760) raises the int/str-limit `ValueError`
(`int(self._int)`, Objects/longobject.c), whatever the first operand (a non-NaN); and an infinite
first operand with `n` out of `[-2·(Emax+prec), 2·(Emax+prec)]` signals InvalidOperation, the range
test coming before the infinity test (:3760-3764). -/
def ScalebRestExact : Prop :=
  ∀ (c : Ctx) (fl : List Signal),
    (∀ a b : Dec, nanKind a ≠ 0 ∨ nanKind b ≠ 0 → (scaleb c a b).run fl = nanSpec2 c a b fl) ∧
    (∀ (a : Dec) (bn : Bool) (bc : Nat), nanKind a = 0 → maxStrDigits < numDigits bc →
      (scaleb c a (.fin bn bc 0)).run fl = .error (.valueError (limitToIntMsg (numDigits bc)))) ∧
    (∀ (neg bn : Bool) (bc : Nat), numDigits bc ≤ maxStrDigits →
      let n : Int := if bn then -(bc : Int) else bc
      ¬(-(2 * (c.emax + c.prec)) ≤ n ∧ n ≤ 2 * (c.emax + c.prec)) →
      (scaleb c (.inf neg) (.fin bn bc 0)).run fl = afterSig c .invalidOperation fl (.nan false false 0))

theorem scalebRestExact_proven : ScalebRestExact := by
  intro c fl
  have hrun : ∀ a b, scaleb c a b = (intArg c a b (-(2 * (c.emax + c.prec))) (2 * (c.emax + c.prec)) >>=
      fun r => match r with
        | .inl r => pure r
        | .inr n => match a with
          | .fin neg co e => fix c (.fin neg co (e + n))
          | d => pure d) := fun _ _ => rfl
  refine ⟨fun a b h => ?_, fun a bn bc ha hl => ?_, fun neg bn bc hl => ?_⟩
  · rw [hrun]
    simp only [intArg, bind_assoc]
    exact checkNans_return c a b fl _ (fun d => by simp [pure_bind]) h
  · rw [hrun]
    simp only [intArg, bind_assoc]
    rw [checkNans_none_bind c a _ ha rfl]
    simp only [intLimit, show numDigits bc > maxStrDigits from hl, ↓reduceIte]
    rfl
  · dsimp only
    intro hr
    rw [hrun, intArg_run c _ bn bc _ _ _ fl rfl hl]
    simp only [hr, not_false_eq_true, ↓reduceIte]
    rw [bind_pure]; exact invalid_run c fl

/-! ## `fma`: the special products, added to `t` -/

/-- `__add__` (_pydecimal.py:1202-1225) of an infinity and `t`: a NaN `t` goes through
`_check_nans` (a signaling one signals InvalidOperation); the opposite infinity is InvalidOperation
('-INF + INF'); anything else gives the infinity. -/
def addInfSpec (c : Ctx) (s : Bool) (t : Dec) (fl : List Signal) : Py (Dec × List Signal) :=
  match t with
  | .nan _ true _ => afterSig c .invalidOperation fl (quietNaN c t)
  | .nan _ false _ => .ok (quietNaN c t, fl)
  | .inf nt => if s ≠ nt then afterSig c .invalidOperation fl (.nan false false 0) else .ok (.inf s, fl)
  | .fin _ _ _ => .ok (.inf s, fl)

/-- The special products of `fma` (_pydecimal.py:1986-2017), which the earlier statement gives only
as `__add__` of the product: with no signaling NaN operand, a quiet NaN `a` (else `b`) is the
product, and `__add__`'s `_check_nans` returns it quieted unless `t` is a signaling NaN, which
signals InvalidOperation and is returned quiet (`nanSpec2 c a t`); an infinity times an infinity or
a non-zero finite value is the infinity of the product's sign added to `t` (`addInfSpec`). -/
def FmaSpecialExact : Prop :=
  ∀ (c : Ctx) (fl : List Signal) (t : Dec),
    (∀ (n : Bool) (p : Nat) (b : Dec), nanKind b ≠ 2 →
      (fma c (.nan n false p) b t).run fl = nanSpec2 c (.nan n false p) t fl) ∧
    (∀ (a : Dec) (n : Bool) (p : Nat), nanKind a = 0 →
      (fma c a (.nan n false p) t).run fl = nanSpec2 c (.nan n false p) t fl) ∧
    (∀ na nb : Bool, (fma c (.inf na) (.inf nb) t).run fl = addInfSpec c (na != nb) t fl) ∧
    (∀ (na sb : Bool) (cb : Nat) (eb : Int), cb ≠ 0 →
      (fma c (.inf na) (.fin sb cb eb) t).run fl = addInfSpec c (na != sb) t fl ∧
      (fma c (.fin sb cb eb) (.inf na) t).run fl = addInfSpec c (sb != na) t fl)

theorem add_inf_run (c : Ctx) (s : Bool) (t : Dec) (fl : List Signal) :
    (add c (.inf s) t).run fl = addInfSpec c s t fl := by
  rcases t with ⟨_, _, _⟩ | nt | ⟨_, st, _⟩
  · simp [add, checkNans, addInfSpec]; rfl
  · by_cases h : s = nt
    · subst h; simp [add, checkNans, addInfSpec]; rfl
    · simp [add, checkNans, addInfSpec, h]; exact invalid_run c fl
  · cases st
    · simp [add, checkNans, addInfSpec, quietNaN, fixNan_spec]; rfl
    · simp only [add, checkNans, addInfSpec, quietNaN]
      rw [bind_assoc]; simp only [pure_bind]; rw [raiseSig_then, fixNan_spec]

theorem add_qnan_run (c : Ctx) (n : Bool) (p : Nat) (t : Dec) (fl : List Signal) :
    (add c (.nan n false p) t).run fl = nanSpec2 c (.nan n false p) t fl := by
  rcases t with ⟨_, _, _⟩ | _ | ⟨_, _, _⟩ <;>
    (simp only [add]; exact checkNans_return c _ _ fl _ (fun d => rfl) (Or.inl (by simp [nanKind])))

theorem fmaSpecialExact_proven : FmaSpecialExact := by
  intro c fl t
  refine ⟨fun n p b hb => ?_, fun a n p ha => ?_, fun na nb => ?_, fun na sb cb eb hc => ?_⟩
  · rw [← add_qnan_run]
    rcases b with ⟨_, _, _⟩ | _ | ⟨_, s, _⟩
    · simp [fma, isSnan, isQnan, isnan, nanKind]
    · simp [fma, isSnan, isQnan, isnan, nanKind]
    · cases s
      · simp [fma, isSnan, isQnan, isnan, nanKind]
      · simp [nanKind] at hb
  · rw [← add_qnan_run]
    rcases a with ⟨_, _, _⟩ | _ | ⟨_, s, _⟩
    · simp [fma, isSnan, isQnan, isnan, nanKind]
    · simp [fma, isSnan, isQnan, isnan, nanKind]
    · cases s <;> simp [nanKind] at ha
  · rw [← add_inf_run]
    simp [fma, isSnan, isQnan, isnan, nanKind, isinfinity, decBool, isZero, Dec.neg]
  · have hz : isZero (.fin sb cb eb) = false := by
      cases cb with
      | zero => exact absurd rfl hc
      | succ n => rfl
    refine ⟨?_, ?_⟩
    · rw [← add_inf_run]
      cases na <;> simp [fma, isSnan, isQnan, isnan, nanKind, isinfinity, decBool, hz, Dec.neg]
    · rw [← add_inf_run]
      cases na <;> simp [fma, isSnan, isQnan, isnan, nanKind, isinfinity, decBool, hz, Dec.neg]

/-! ## `abs(round=False)` -/

/-- `__abs__(round=False)` (_pydecimal.py:1187-1188) is `copy_abs()`: the operand with its sign
cleared, unrounded, with no flag, a NaN included (no `_check_nans`, no signal for a signaling
NaN). -/
def AbsNoRoundExact : Prop :=
  ∀ (c : Ctx) (fl : List Signal),
    (∀ (neg : Bool) (co : Nat) (e : Int), (dunderAbs c (.fin neg co e) false).run fl = .ok (.fin false co e, fl)) ∧
    (∀ neg : Bool, (dunderAbs c (.inf neg) false).run fl = .ok (.inf false, fl)) ∧
    (∀ (neg s : Bool) (p : Nat), (dunderAbs c (.nan neg s p) false).run fl = .ok (.nan false s p, fl))

theorem absNoRoundExact_proven : AbsNoRoundExact :=
  fun _ _ => ⟨fun _ _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-! ## `compare_total_mag` -/

/-- `compare_total_mag` (_pydecimal.py:3072-3082), the parts `CompareTotalExact` leaves:
it is antisymmetric, and a number against a NaN of either sign is `-1`. -/
def CompareTotalMagRest : Prop :=
  (∀ a b : Dec, compareTotalMag b a = -compareTotalMag a b) ∧
  (∀ (x : Dec) (n s : Bool) (p : Nat), nanKind x = 0 → compareTotalMag x (.nan n s p) = -1)

theorem compareTotalMagRest_proven : CompareTotalMagRest := by
  have hT := compareTotalExact_proven
  have anti : ∀ a b : Dec, compareTotalMag b a = -compareTotalMag a b := fun a b =>
    (hT.1 (copyAbs a) (copyAbs b)).1
  refine ⟨anti, fun x n s p hx => ?_⟩
  rw [anti, hT.2.2.2.2.2.2.2.2.2.2.1 n s p x hx]

/-! ## `_convert_other` of a tuple, with `raiseit` -/

/-- `_convert_other(t, raiseit=True)` for a tuple `t` (_pydecimal.py:6111-6112) raises what
`raise TypeError("Unable to convert %s to Decimal" % t)` raises, `%` taking the tuple as its
argument tuple (Objects/unicode_format.c): "not enough arguments for format string (got 0)" for
`()`; for a first element whose `str()` raises (`(10**5000,)`, `(10**5000, 1)`), that exception;
the `TypeError` with the formatted message for a 1-tuple that prints; and "not all arguments
converted during string formatting (required 1, got k)" for k >= 2 elements whose first prints.
With `raiseit=False` a tuple is `NotImplemented` (`ConvertOtherExact`). -/
def ConvertOtherTupleExact : Prop :=
  convertOther true (.tuple []) = .error (.typeError "not enough arguments for format string (got 0)") ∧
  (∀ (e : PyExc) (rest : List StrErr), convertOther true (.tuple (some e :: rest)) = .error e) ∧
  convertOther true (.tuple [none]) = .error (.typeError unableMsg) ∧
  ∀ (x : StrErr) (rest : List StrErr), convertOther true (.tuple (none :: x :: rest)) =
    .error (.typeError s!"not all arguments converted during string formatting (required 1, got {rest.length + 2})")

theorem convertOtherTupleExact_proven : ConvertOtherTupleExact :=
  ⟨rfl, fun _ _ => rfl, rfl, fun _ _ => rfl⟩

/-! ## `remainder_near`: the branches `RemainderNearExact` leaves -/

/-- `remainder_near(a, b)` (_pydecimal.py:1550-1625), every branch `RemainderNearExact` does not
state, for every `math.log10` (none of them reaches `_is_less_than_pow10a`): a NaN operand goes
through `_check_nans` (:1559-1561), `nanSpec2`, before the infinity and zero tests; a zero `a` with a
non-zero finite `b` is the zero of `a`'s sign at the ideal exponent `min(ea, eb)` through `_fix`
(:1580-1584), and with an infinite `b` it is `a` through `_fix` (:1576-1578); for non-zero finite
operands whose adjusted exponents differ by `prec + 1` or more the result is InvalidOperation
(DivisionImpossible, :1588-1590), and by `-2` or less (`|a/b| < 0.1`, so the nearest integer is 0)
it is `a` itself, rescaled to the ideal exponent by padding zeros (exact), through `_fix`
(:1591-1594); in between, `_WorkRep` (:1597-1598) takes `int(self._int)` and `int(other._int)`, which
raise the int/str-limit `ValueError` for a coefficient of more than 4300 digits, `a`'s first. -/
def RemainderNearRest : Prop :=
  ∀ (lg : Nat → Binary64.F64) (c : Ctx) (fl : List Signal),
    (∀ a b : Dec, nanKind a ≠ 0 ∨ nanKind b ≠ 0 → (remainderNearL lg c a b).run fl = nanSpec2 c a b fl) ∧
    (∀ (sa : Bool) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int), cb ≠ 0 →
      (remainderNearL lg c (.fin sa 0 ea) (.fin sb cb eb)).run fl = (fix c (.fin sa 0 (min ea eb))).run fl) ∧
    (∀ (sa : Bool) (ea : Int) (nb : Bool),
      (remainderNearL lg c (.fin sa 0 ea) (.inf nb)).run fl = (fix c (.fin sa 0 ea)).run fl) ∧
    (∀ (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int), ca ≠ 0 → cb ≠ 0 →
      c.prec + 1 ≤ (ea + numDigits ca - 1) - (eb + numDigits cb - 1) →
      (remainderNearL lg c (.fin sa ca ea) (.fin sb cb eb)).run fl =
        afterSig c .invalidOperation fl (.nan false false 0)) ∧
    (∀ (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int), ca ≠ 0 → cb ≠ 0 →
      (ea + numDigits ca - 1) - (eb + numDigits cb - 1) ≤ -2 →
      (remainderNearL lg c (.fin sa ca ea) (.fin sb cb eb)).run fl =
        (fix c (.fin sa (ca * 10 ^ (ea - min ea eb).toNat) (min ea eb))).run fl) ∧
    (∀ (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int), ca ≠ 0 → cb ≠ 0 →
      -2 < (ea + numDigits ca - 1) - (eb + numDigits cb - 1) →
      (ea + numDigits ca - 1) - (eb + numDigits cb - 1) < c.prec + 1 →
      maxStrDigits < numDigits ca →
      (remainderNearL lg c (.fin sa ca ea) (.fin sb cb eb)).run fl =
        .error (.valueError (limitToIntMsg (numDigits ca)))) ∧
    (∀ (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int), ca ≠ 0 → cb ≠ 0 →
      -2 < (ea + numDigits ca - 1) - (eb + numDigits cb - 1) →
      (ea + numDigits ca - 1) - (eb + numDigits cb - 1) < c.prec + 1 →
      numDigits ca ≤ maxStrDigits → maxStrDigits < numDigits cb →
      (remainderNearL lg c (.fin sa ca ea) (.fin sb cb eb)).run fl =
        .error (.valueError (limitToIntMsg (numDigits cb))))

theorem remainderNearRest_proven : RemainderNearRest := by
  intro lg c fl
  have hz : ∀ (s : Bool) (co : Nat) (e : Int), co ≠ 0 → decBool (.fin s co e) = true := by
    intro s co e hc; cases co with
    | zero => exact absurd rfl hc
    | succ n => rfl
  refine ⟨fun a b h => ?_, fun sa ea sb cb eb hb => ?_, fun sa ea nb => ?_,
    fun sa ca ea sb cb eb ha hb h1 => ?_, fun sa ca ea sb cb eb ha hb h1 => ?_,
    fun sa ca ea sb cb eb ha hb h1 h2 hl => ?_, fun sa ca ea sb cb eb ha hb h1 h2 hl1 hl => ?_⟩
  · unfold remainderNearL
    exact checkNans_return c a b fl _ (fun d => rfl) h
  · simp only [remainderNearL]
    rw [checkNans_none_bind c _ _ rfl rfl]
    have h0 : decBool (.fin sa 0 ea) = false := rfl
    simp only [isinfinity, hz sb cb eb hb, h0, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false, expOf, Dec.neg]
    try rw [bind_pure]
  · simp only [remainderNearL]
    rw [checkNans_none_bind c _ _ rfl rfl]
    simp only [isinfinity, decBool, isZero, Bool.not_true, Bool.not_false, ↓reduceIte, ne_eq,
      not_true_eq_false, Bool.false_eq_true]
    cases nb <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.reduceNeg, Int.reduceEq, not_false_eq_true] <;>
      (rw [bind_pure])
  · simp only [remainderNearL, bind_assoc]
    rw [checkNans_none_bind c _ _ rfl rfl]
    simp only [isinfinity, hz sb cb eb hb, hz sa ca ea ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      ne_eq, not_true_eq_false, expOf, Dec.adjusted, adjustedD]
    simp only [show ea + numDigits ca - 1 - (eb + numDigits cb - 1) ≥ c.prec + 1 by omega, ↓reduceIte]
    try rw [bind_pure]
    exact invalid_run c fl
  · simp only [remainderNearL, bind_assoc]
    rw [checkNans_none_bind c _ _ rfl rfl]
    simp only [isinfinity, hz sb cb eb hb, hz sa ca ea ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      ne_eq, not_true_eq_false, expOf, Dec.adjusted, adjustedD]
    have hp : c.prec ≥ 0 := Nat.zero_le _
    simp only [show ¬ (ea + numDigits ca - 1 - (eb + numDigits cb - 1) ≥ c.prec + 1) by omega,
      show ea + numDigits ca - 1 - (eb + numDigits cb - 1) ≤ -2 from h1, ↓reduceIte]
    have hr : rescale (.fin sa ca ea) (min ea eb) c.rounding =
        .ok (.fin sa (ca * 10 ^ (ea - min ea eb).toNat) (min ea eb)) := by
      simp only [rescale, ha, ↓reduceIte, show ea ≥ min ea eb by omega]
    rw [liftPy_run, hr]
    try simp only []
    try rw [bind_pure]
  · simp only [remainderNearL, bind_assoc]
    rw [checkNans_none_bind c _ _ rfl rfl]
    simp only [isinfinity, hz sb cb eb hb, hz sa ca ea ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      ne_eq, not_true_eq_false, expOf, Dec.adjusted, adjustedD]
    simp only [show ¬ (ea + numDigits ca - 1 - (eb + numDigits cb - 1) ≥ c.prec + 1) by omega,
      show ¬ (ea + numDigits ca - 1 - (eb + numDigits cb - 1) ≤ -2) by omega, ↓reduceIte]
    have w1 : workRep (.fin sa ca ea) = .error (.valueError (limitToIntMsg (numDigits ca))) := by
      simp [workRep, intLimit, show numDigits ca > maxStrDigits from hl, bind, Except.bind]
    rw [liftPy_run, w1]
  · simp only [remainderNearL, bind_assoc]
    rw [checkNans_none_bind c _ _ rfl rfl]
    simp only [isinfinity, hz sb cb eb hb, hz sa ca ea ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      ne_eq, not_true_eq_false, expOf, Dec.adjusted, adjustedD]
    simp only [show ¬ (ea + numDigits ca - 1 - (eb + numDigits cb - 1) ≥ c.prec + 1) by omega,
      show ¬ (ea + numDigits ca - 1 - (eb + numDigits cb - 1) ≤ -2) by omega, ↓reduceIte]
    have w1 : workRep (.fin sa ca ea) = .ok (sa, ca, ea) := by
      simp [workRep, intLimit, show ¬ numDigits ca > maxStrDigits by omega, bind, Except.bind, pure, Except.pure]
    have w2 : workRep (.fin sb cb eb) = .error (.valueError (limitToIntMsg (numDigits cb))) := by
      simp [workRep, intLimit, show numDigits cb > maxStrDigits from hl, bind, Except.bind]
    rw [liftPy_run, w1]
    simp only []
    rw [liftPy_run, w2]

end PyLean.Decimal
