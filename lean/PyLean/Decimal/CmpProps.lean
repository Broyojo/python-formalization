import PyLean.Decimal.OpsProps

/-!
`_cmp` against the exact order of the values, and the NaN checks every comparison
runs first (`_check_nans`, `_compare_check_nans`, `_fix_nan`).

The numeric order is stated without `_cmp`'s algorithm (adjusted exponents, then the
zero-padded digit strings): two finite values `±c1·10^e1`, `±c2·10^e2` are compared
as the integers `±c1·10^(e1-m)` and `±c2·10^(e2-m)` for `m = min(e1, e2)`, and
`-Infinity` is below and `Infinity` above every finite value.
-/

namespace PyLean.Decimal

open PyLean

/-! ## The exact order -/

/-- The order of two integers. -/
def ordOf (x y : Int) : Ordering := if x < y then .lt else if x = y then .eq else .gt

/-- `±c` as an integer. -/
def sgnVal (neg : Bool) (c : Nat) : Int := if neg then -(c : Int) else c

/-- The order of `±c1·10^e1` and `±c2·10^e2`, both scaled to the lower exponent. -/
def finOrder (n1 : Bool) (c1 : Nat) (e1 : Int) (n2 : Bool) (c2 : Nat) (e2 : Int) : Ordering :=
  let m := min e1 e2
  ordOf (sgnVal n1 (c1 * 10 ^ (e1 - m).toNat)) (sgnVal n2 (c2 * 10 ^ (e2 - m).toNat))

/-- The numeric order of two decimals that are not NaNs. -/
def numOrder : Dec → Dec → Ordering
  | .fin n1 c1 e1, .fin n2 c2 e2 => finOrder n1 c1 e1 n2 c2 e2
  | .inf n1, .inf n2 => if n1 = n2 then .eq else if n1 then .lt else .gt
  | .inf n1, _ => if n1 then .lt else .gt
  | _, .inf n2 => if n2 then .gt else .lt
  | _, _ => .eq

theorem cmpVal_fin_exact (n1 n2 : Bool) (c1 c2 : Nat) (e1 e2 : Int) :
    cmpVal (.fin n1 c1 e1) (.fin n2 c2 e2) = finOrder n1 c1 e1 n2 c2 e2 := by
  have hA : (e1 - min e1 e2).toNat = (e1 - e2).toNat := by omega
  have hB : (e2 - min e1 e2).toNat = (e2 - e1).toNat := by omega
  have p1 : 0 < 10 ^ (e1 - e2).toNat := Nat.pow_pos (by decide)
  have p2 : 0 < 10 ^ (e2 - e1).toNat := Nat.pow_pos (by decide)
  have gt12 : c1 = 0 ∨ c2 = 0 ∨ ¬ (e1 + (numDigits c1 : Int) - 1 > e2 + numDigits c2 - 1) ∨
      c2 * 10 ^ (e2 - e1).toNat < c1 * 10 ^ (e1 - e2).toNat := by
    by_cases h1 : c1 = 0
    · exact Or.inl h1
    by_cases h2 : c2 = 0
    · exact Or.inr (Or.inl h2)
    by_cases h : e1 + (numDigits c1 : Int) - 1 > e2 + numDigits c2 - 1
    · exact Or.inr (Or.inr (Or.inr (scaled_ne h2 h1 (by omega))))
    · exact Or.inr (Or.inr (Or.inl h))
  have lt12 : c1 = 0 ∨ c2 = 0 ∨ ¬ (e1 + (numDigits c1 : Int) - 1 < e2 + numDigits c2 - 1) ∨
      c1 * 10 ^ (e1 - e2).toNat < c2 * 10 ^ (e2 - e1).toNat := by
    by_cases h1 : c1 = 0
    · exact Or.inl h1
    by_cases h2 : c2 = 0
    · exact Or.inr (Or.inl h2)
    by_cases h : e1 + (numDigits c1 : Int) - 1 < e2 + numDigits c2 - 1
    · exact Or.inr (Or.inr (Or.inr (scaled_ne h1 h2 (by omega))))
    · exact Or.inr (Or.inr (Or.inl h))
  have z1 : (c1 = 0 ∧ c1 * 10 ^ (e1 - e2).toNat = 0) ∨ (c1 ≠ 0 ∧ 0 < c1 * 10 ^ (e1 - e2).toNat) := by
    by_cases h : c1 = 0
    · left; subst h; simp
    · right; exact ⟨h, Nat.mul_pos (Nat.pos_of_ne_zero h) p1⟩
  have z2 : (c2 = 0 ∧ c2 * 10 ^ (e2 - e1).toNat = 0) ∨ (c2 ≠ 0 ∧ 0 < c2 * 10 ^ (e2 - e1).toNat) := by
    by_cases h : c2 = 0
    · left; subst h; simp
    · right; exact ⟨h, Nat.mul_pos (Nat.pos_of_ne_zero h) p2⟩
  simp only [finOrder, hA, hB, cmpVal]
  generalize c1 * 10 ^ (e1 - e2).toNat = P1 at *
  generalize c2 * 10 ^ (e2 - e1).toNat = P2 at *
  cases n1 <;> cases n2 <;>
    simp only [signOrd, Ordering.swap, sgnVal, ordOf, Bool.not_true, Bool.not_false, Bool.and_false,
      Bool.and_true, Bool.false_eq_true, ↓reduceIte] <;>
    (repeat' split) <;> first | rfl | (exfalso; omega)

/-- `_cmp` is the numeric order, for all operands that are not NaNs. -/
theorem cmpVal_exact (a b : Dec) (ha : nanKind a = 0) (hb : nanKind b = 0) :
    cmpVal a b = numOrder a b := by
  cases a with
  | nan n s p => cases s <;> simp [nanKind] at ha
  | inf n1 =>
    cases b with
    | nan n s p => cases s <;> simp [nanKind] at hb
    | inf n2 => rfl
    | fin n2 c2 e2 => rfl
  | fin n1 c1 e1 =>
    cases b with
    | nan n s p => cases s <;> simp [nanKind] at hb
    | inf n2 => rfl
    | fin n2 c2 e2 => exact cmpVal_fin_exact n1 n2 c1 c2 e1 e2

/-! ## `_fix_nan` -/

/-- The number of payload digits a NaN keeps: `prec - clamp`. -/
def nanDigits (c : Ctx) : Nat := c.prec - (if c.clamp then 1 else 0)

/-- `_fix_nan` keeps the last `prec - clamp` digits of the payload, with leading zeros
dropped (_pydecimal.py:1703-1711), so the payload becomes `p mod 10^(prec - clamp)`;
the sign and the NaN kind are kept. -/
theorem fixNan_spec (c : Ctx) (neg sig : Bool) (p : Nat) :
    fixNan c neg sig p = .nan neg sig (p % 10 ^ nanDigits c) := by
  simp only [fixNan, nanDigits]
  generalize c.prec - (if c.clamp then 1 else 0) = k
  by_cases h : numDigits p > k ∧ p ≠ 0
  · rw [if_pos h]
  · rw [if_neg h]
    by_cases hp : p = 0
    · subst hp; simp
    · have hle : numDigits p ≤ k := by omega
      have hpos : 0 < k := Nat.lt_of_lt_of_le (numDigits_pos p) hle
      rw [Nat.mod_eq_of_lt ((numDigits_le_iff hpos).mp hle)]

/-! ## Signals -/

/-- The flags after `s` is flagged. -/
def addFlag (s : Signal) (fl : List Signal) : List Signal := if s ∈ fl then fl else fl ++ [s]

/-- The outcome of signalling `s` and then returning `v`: the signal's exception if it is
trapped, otherwise `v` with `s` flagged. -/
def afterSig {β : Type} (c : Ctx) (s : Signal) (fl : List Signal) (v : β) : Py (β × List Signal) :=
  if s ∈ c.traps then .error (.named s.name "~") else .ok (v, addFlag s fl)

theorem raiseSig_then {β : Type} (c : Ctx) (s : Signal) (fl : List Signal) (v : β) :
    (do raiseSig c s; (pure v : DM β)).run fl = afterSig c s fl v := by
  unfold afterSig addFlag
  by_cases h : s ∈ c.traps <;>
    simp [raiseSig, h, StateT.run, bind, StateT.bind, Except.bind, modify, modifyGet,
      MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw, StateT.lift, Except.tryCatch]

/-- The quiet NaN an operation returns for a NaN operand. -/
def quietNaN (c : Ctx) : Dec → Dec
  | .nan neg _ p => .nan neg false (p % 10 ^ nanDigits c)
  | d => d

theorem quietOf_eq (c : Ctx) (d : Dec) : quietOf c d = quietNaN c d := by
  cases d with
  | nan n s p => simp only [quietOf, quietNaN, fixNan_spec]
  | _ => rfl

/-- `_check_nans`, _pydecimal.py:790-820: a signaling NaN on either side signals
InvalidOperation and returns that operand quieted, the left one first; otherwise a quiet
NaN is returned quieted (the left one first) with no flag; with no NaN, nothing. -/
def CheckNansExact : Prop :=
  ∀ (c : Ctx) (a b : Dec) (fl : List Signal),
    (nanKind a = 2 → (checkNans c a (some b)).run fl = afterSig c .invalidOperation fl (some (quietNaN c a))) ∧
    (nanKind a ≠ 2 → nanKind b = 2 →
      (checkNans c a (some b)).run fl = afterSig c .invalidOperation fl (some (quietNaN c b))) ∧
    (nanKind a = 1 → nanKind b ≠ 2 → (checkNans c a (some b)).run fl = .ok (some (quietNaN c a), fl)) ∧
    (nanKind a = 0 → nanKind b = 1 → (checkNans c a (some b)).run fl = .ok (some (quietNaN c b), fl)) ∧
    (nanKind a = 0 → nanKind b = 0 → (checkNans c a (some b)).run fl = .ok (none, fl)) ∧
    (nanKind a = 2 → (checkNans c a none).run fl = afterSig c .invalidOperation fl (some (quietNaN c a))) ∧
    (nanKind a = 1 → (checkNans c a none).run fl = .ok (some (quietNaN c a), fl)) ∧
    (nanKind a = 0 → (checkNans c a none).run fl = .ok (none, fl))

theorem checkNansExact_proven : CheckNansExact := by
  intro c a b fl
  refine ⟨fun ha => ?_, fun ha hb => ?_, fun ha hb => ?_, fun ha hb => ?_, fun ha hb => ?_,
    fun ha => ?_, fun ha => ?_, fun ha => ?_⟩
  · cases a with
    | nan n s p =>
      cases s
      · simp [nanKind] at ha
      · simp only [checkNans, quietNaN, ← fixNan_spec]; exact raiseSig_then _ _ _ _
    | _ => simp [nanKind] at ha
  · cases b with
    | nan n s p =>
      cases s
      · simp [nanKind] at hb
      · cases a with
        | nan m t q =>
          cases t
          · simp only [checkNans, quietNaN, ← fixNan_spec]; exact raiseSig_then _ _ _ _
          · simp [nanKind] at ha
        | inf m => simp only [checkNans, quietNaN, ← fixNan_spec]; exact raiseSig_then _ _ _ _
        | fin m q e => simp only [checkNans, quietNaN, ← fixNan_spec]; exact raiseSig_then _ _ _ _
    | _ => simp [nanKind] at hb
  · cases a with
    | nan n s p =>
      cases s
      · cases b with
        | nan m t q => cases t <;> simp_all [nanKind, checkNans, quietNaN, fixNan_spec] <;> rfl
        | _ => simp [checkNans, quietNaN, fixNan_spec] <;> rfl
      · simp [nanKind] at ha
    | _ => simp [nanKind] at ha
  · cases b with
    | nan n s p =>
      cases s
      · cases a with
        | nan m t q => cases t <;> simp [nanKind] at ha
        | _ => simp [checkNans, quietNaN, fixNan_spec] <;> rfl
      · simp [nanKind] at hb
    | _ => simp [nanKind] at hb
  · cases a with
    | nan n s p => cases s <;> simp [nanKind] at ha
    | _ =>
      cases b with
      | nan n s p => cases s <;> simp [nanKind] at hb
      | _ => rfl
  · cases a with
    | nan n s p =>
      cases s
      · simp [nanKind] at ha
      · simp only [checkNans, quietNaN, ← fixNan_spec]; exact raiseSig_then _ _ _ _
    | _ => simp [nanKind] at ha
  · cases a with
    | nan n s p =>
      cases s
      · simp [checkNans, quietNaN, fixNan_spec] <;> rfl
      · simp [nanKind] at ha
    | _ => simp [nanKind] at ha
  · cases a with
    | nan n s p => cases s <;> simp [nanKind] at ha
    | _ => rfl

end PyLean.Decimal
