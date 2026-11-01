import PyLean.Decimal.Ops
import PyLean.Decimal.Quantize
import PyLean.Decimal.RoundTrip

/-! Properties of the methods in `Ops.lean`. -/

namespace PyLean.Decimal

open PyLean

/-! ## Sign operations -/

theorem withSign_withSign (d : Dec) (x y : Bool) : (d.withSign x).withSign y = d.withSign y := by
  cases d <;> rfl

theorem neg_withSign (d : Dec) (x : Bool) : (d.withSign x).neg = x := by cases d <;> rfl

theorem withSign_neg (d : Dec) : d.withSign d.neg = d := by cases d <;> rfl

/-- `copy_negate` is an involution that flips the sign, `copy_abs` clears it and is
idempotent, `copy_sign` takes its sign from the second operand and its magnitude
from the first, and `compare_total_mag` is `compare_total` on the magnitudes. -/
def CopyOpsCorrect : Prop :=
  ∀ a b : Dec,
    copyNegate (copyNegate a) = a ∧ (copyNegate a).neg = !a.neg ∧
    (copyAbs a).neg = false ∧ copyAbs (copyAbs a) = copyAbs a ∧
    (copySign a b).neg = b.neg ∧ copyAbs (copySign a b) = copyAbs a ∧
    compareTotalMag a b = compareTotal (copyAbs a) (copyAbs b) ∧
    compareTotalMag a a = 0 ∧ compareTotalMag b a = -compareTotalMag a b

theorem copyOpsCorrect_proven : CopyOpsCorrect := by
  intro a b
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · simp only [copyNegate, negate, withSign_withSign, neg_withSign, Bool.not_not, withSign_neg]
  · exact neg_withSign _ _
  · exact neg_withSign _ _
  · simp only [copyAbs, withSign_withSign]
  · exact neg_withSign _ _
  · simp only [copyAbs, copySign, withSign_withSign]
  · exact (compareTotal_eq_zero _ _).mpr rfl
  · exact compareTotal_antisymm _ _

/-! ## Classification -/

/-- For every context and decimal: exactly one class of `number_class` applies and
it agrees with the predicates; `bool(d)` is `not is_zero`; `is_finite`,
`is_infinite` and `is_nan` partition the values; `is_normal` and `is_subnormal`
partition the finite non-zero values. -/
def ClassificationCorrect : Prop :=
  ∀ (c : Ctx) (d : Dec),
    (numberClass c d = "sNaN" ↔ isSnan d = true) ∧
    (numberClass c d = "NaN" ↔ isQnan d = true) ∧
    (isNanP d = true ↔ isQnan d = true ∨ isSnan d = true) ∧
    decBool d = !isZero d ∧
    ((isFinite d = true ∧ isInfinite d = false ∧ isNanP d = false) ∨
     (isFinite d = false ∧ isInfinite d = true ∧ isNanP d = false) ∨
     (isFinite d = false ∧ isInfinite d = false ∧ isNanP d = true)) ∧
    (isFinite d = true → isZero d = false → (isNormal c d != isSubnormal c d) = true) ∧
    isCanonical d = true

theorem classificationCorrect_proven : ClassificationCorrect := by
  intro c d
  cases d with
  | nan n s p =>
    cases s <;> cases n <;>
      simp [numberClass, isSnan, isQnan, isNanP, isnan, nanKind, isFinite, isInfinite, isinfinity,
        isSpecial, decBool, isZero, isCanonical]
  | inf n =>
    cases n <;>
      simp [numberClass, isSnan, isQnan, isNanP, isnan, nanKind, isFinite, isInfinite, isinfinity,
        isSpecial, decBool, isZero, isCanonical]
  | fin n co e =>
    have hna : ∀ s : String, ¬ ((if isZero (Dec.fin n co e) = true then (if n = true then "-Zero" else "+Zero")
        else if isSubnormal c (.fin n co e) = true then (if n = true then "-Subnormal" else "+Subnormal")
        else if n = true then "-Normal" else "+Normal") = s) ∨ s ≠ "sNaN" ∧ s ≠ "NaN" := by
      intro s
      by_cases h : s = "sNaN" ∨ s = "NaN"
      · left
        rcases h with rfl | rfl <;> (repeat' split) <;> decide
      · right
        exact ⟨fun e => h (Or.inl e), fun e => h (Or.inr e)⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · constructor
      · intro h
        exfalso
        have := (hna "sNaN").resolve_right (by simp)
        simp only [numberClass, isSnan, isQnan, isnan, nanKind, isinfinity] at h
        simp at h
        exact this h
      · intro h; simp [isSnan, isnan, nanKind] at h
    · constructor
      · intro h
        exfalso
        have := (hna "NaN").resolve_right (by simp)
        simp only [numberClass, isSnan, isQnan, isnan, nanKind, isinfinity] at h
        simp at h
        exact this h
      · intro h; simp [isQnan, isnan, nanKind] at h
    · simp [isNanP, isQnan, isSnan, isnan, nanKind]
    · rfl
    · left
      simp [isFinite, isInfinite, isNanP, isSpecial, isnan, nanKind, isinfinity]
    · intro _ hz
      have hb : decBool (.fin n co e) = true := by simp [decBool, hz]
      simp only [isNormal, isSubnormal, isSpecial, hb, Bool.not_true, Bool.or_self, Bool.false_eq_true,
        ↓reduceIte]
      by_cases h : (Dec.fin n co e).adjusted < c.emin
      · simp [h, Int.not_le.mpr h]
      · simp [h, Int.not_lt.mp h]

/-! ## Comparisons -/

theorem cmpInt_swap (a b : Dec) (ha : nanKind a = 0) (hb : nanKind b = 0) : cmpInt b a = -cmpInt a b := by
  simp only [cmpInt, cmpVal_swap a b (nanKind_zero ha) (nanKind_zero hb)]
  cases cmpVal a b <;> rfl

theorem checkNans_none (c : Ctx) (a b : Dec) (ha : nanKind a = 0) (hb : nanKind b = 0) (fl : List Signal) :
    (checkNans c a (some b)).run fl = .ok (none, fl) := by
  cases a with
  | nan n s p => cases s <;> simp [nanKind] at ha
  | _ =>
    cases b with
    | nan n s p => cases s <;> simp [nanKind] at hb
    | _ => rfl

theorem compareCheckNans_none (c : Ctx) (a b : Dec) (ha : nanKind a = 0) (hb : nanKind b = 0)
    (fl : List Signal) : (compareCheckNans c a b).run fl = .ok (none, fl) := by
  cases a with
  | nan n s p => cases s <;> simp [nanKind] at ha
  | _ =>
    cases b with
    | nan n s p => cases s <;> simp [nanKind] at hb
    | _ => rfl

/-- For non-NaN operands, `==`, `<`, `<=`, `>`, `>=` follow `_cmp`, raise no flag,
and `compare` returns `_cmp` as a Decimal, antisymmetrically. An ordering with a
quiet NaN sets InvalidOperation; `==` with a quiet NaN is False and sets nothing. -/
def ComparisonsConsistent : Prop :=
  ∀ (c : Ctx) (a b : Dec) (fl : List Signal),
    (nanKind a = 0 → nanKind b = 0 →
      (dunderEq c a b).run fl = .ok (decide (cmpVal a b = .eq), fl) ∧
      (dunderLt c a b).run fl = .ok (decide (cmpVal a b = .lt), fl) ∧
      (dunderLe c a b).run fl = .ok (decide (cmpVal a b ≠ .gt), fl) ∧
      (dunderGt c a b).run fl = .ok (decide (cmpVal a b = .gt), fl) ∧
      (dunderGe c a b).run fl = .ok (decide (cmpVal a b ≠ .lt), fl) ∧
      (compareD c a b).run fl = .ok (decOfInt (cmpInt a b), fl) ∧
      (compareSignal c a b).run fl = .ok (decOfInt (cmpInt a b), fl) ∧
      cmpInt b a = -cmpInt a b) ∧
    (∀ n p, a = .nan n false p → nanKind b ≠ 2 →
      (dunderEq c a b).run fl = .ok (false, fl) ∧
      (∀ r fl', (dunderLt c a b).run fl = .ok (r, fl') → r = false ∧ Signal.invalidOperation ∈ fl'))

theorem bind_run_ok {α β : Type} {x : DM α} {f : α → DM β} {fl fl' : List Signal} {a : α}
    (h : x.run fl = .ok (a, fl')) : (x >>= f).run fl = (f a).run fl' := by
  simp only [StateT.run, bind, StateT.bind, Except.bind] at h ⊢
  rw [h]

theorem dunderEq_run (c : Ctx) (a b : Dec) (fl : List Signal)
    (h : (checkNans c a (some b)).run fl = .ok (none, fl)) :
    (dunderEq c a b).run fl = .ok (cmpInt a b == 0, fl) := by
  simp only [dunderEq]
  rw [bind_run_ok h]
  rfl

theorem dunderOrd_run (test : Int → Bool) (c : Ctx) (a b : Dec) (fl : List Signal)
    (h : (compareCheckNans c a b).run fl = .ok (none, fl)) :
    (dunderOrd test c a b).run fl = .ok (test (cmpInt a b), fl) := by
  simp only [dunderOrd]
  rw [bind_run_ok h]
  rfl

theorem cmpInt_eq (a b : Dec) : (cmpInt a b == 0) = decide (cmpVal a b = .eq) := by
  unfold cmpInt; split <;> simp_all

theorem cmpInt_lt (a b : Dec) : decide (cmpInt a b < 0) = decide (cmpVal a b = .lt) := by
  unfold cmpInt; split <;> simp_all

theorem cmpInt_le (a b : Dec) : decide (cmpInt a b ≤ 0) = decide (cmpVal a b ≠ .gt) := by
  unfold cmpInt; split <;> simp_all

theorem cmpInt_gt (a b : Dec) : decide (cmpInt a b > 0) = decide (cmpVal a b = .gt) := by
  unfold cmpInt; split <;> simp_all

theorem cmpInt_ge (a b : Dec) : decide (cmpInt a b ≥ 0) = decide (cmpVal a b ≠ .lt) := by
  unfold cmpInt; split <;> simp_all

theorem comparisonsConsistent_proven : ComparisonsConsistent := by
  intro c a b fl
  constructor
  · intro ha hb
    have h1 := checkNans_none c a b ha hb fl
    have h2 := compareCheckNans_none c a b ha hb fl
    have hc : (compareD c a b).run fl = .ok (decOfInt (cmpInt a b), fl) := by
      unfold compareD
      by_cases hs : (isSpecial a || isSpecial b) = true
      · simp only [hs, ↓reduceIte]
        rw [bind_run_ok h1]
        rfl
      · simp only [hs, Bool.false_eq_true, ↓reduceIte]
        rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, hc, ?_, cmpInt_swap a b ha hb⟩
    · rw [dunderEq_run c a b fl h1, cmpInt_eq]
    · exact (dunderOrd_run (fun x => decide (x < 0)) c a b fl h2).trans (by simp only [cmpInt_lt])
    · exact (dunderOrd_run (fun x => decide (x ≤ 0)) c a b fl h2).trans (by simp only [cmpInt_le])
    · exact (dunderOrd_run (fun x => decide (x > 0)) c a b fl h2).trans (by simp only [cmpInt_gt])
    · exact (dunderOrd_run (fun x => decide (x ≥ 0)) c a b fl h2).trans (by simp only [cmpInt_ge])
    · simp only [compareSignal]
      rw [bind_run_ok h2]
      exact hc
  · rintro n p rfl hb
    have hq : (checkNans c (.nan n false p) (some b)).run fl = .ok (some (fixNan c n false p), fl) := by
      cases b with
      | nan m s q => cases s <;> first | rfl | simp [nanKind] at hb
      | _ => rfl
    refine ⟨?_, ?_⟩
    · simp only [dunderEq]
      rw [bind_run_ok hq]
      rfl
    · intro r fl' h
      simp only [dunderLt, dunderOrd] at h
      obtain ⟨x, fl1, h1, h2⟩ := bind_ok h
      have hs : isSnan b = false := by
        cases b with
        | nan m s q => cases s <;> first | rfl | simp [nanKind] at hb
        | _ => rfl
      have e1 : isSpecial (.nan n false p) = true := rfl
      have e2 : isSnan (.nan n false p) = false := rfl
      have e3 : isQnan (.nan n false p) = true := rfl
      have hm : compareCheckNans c (.nan n false p) b =
          (do raiseSig c .invalidOperation; pure (some (quietOf c (.nan n false p)))) := by
        simp only [compareCheckNans, e1, e2, e3, hs, Bool.true_or, ↓reduceIte, Bool.false_eq_true]
      rw [hm] at h1
      obtain ⟨_, fl2, h3, h4⟩ := bind_ok h1
      have h5 := pure_ok h4
      cases h5
      have := pure_ok h2
      cases this
      exact ⟨rfl, ((raiseSig_ok h3).2 _).mpr (Or.inr rfl)⟩

/-! ## `max`, `min` -/

theorem minmaxNans_none (c : Ctx) (a b : Dec) (ha : nanKind a = 0) (hb : nanKind b = 0) (fl : List Signal) :
    (minmaxNans c a b).run fl = .ok (none, fl) := by
  have h1 : isnan a = 0 := ha
  have h2 : isnan b = 0 := hb
  unfold minmaxNans
  by_cases hs : (isSpecial a || isSpecial b) = true
  · simp only [hs, ↓reduceIte, h1, h2, ne_eq, not_true_eq_false, or_self]
    rfl
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    rfl

/-- The result of `max`, `min` etc. on non-NaN operands: `_fix` of the operand
the comparison selects. -/
theorem minmax_run (cmp : Dec → Dec → Int) (lw : Bool) (c : Ctx) (a b : Dec) (ha : nanKind a = 0)
    (hb : nanKind b = 0) (fl : List Signal) :
    (minmaxBy cmp lw c a b).run fl =
      (fix c (let cc := cmp a b
              let cc := if cc = 0 then compareTotal a b else cc
              if cc = -1 then (if lw then a else b) else (if lw then b else a))).run fl := by
  simp only [minmaxBy]
  rw [bind_run_ok (minmaxNans_none c a b ha hb fl)]

theorem cmpInt_cases (a b : Dec) : cmpInt a b = -1 ∨ cmpInt a b = 0 ∨ cmpInt a b = 1 := by
  simp only [cmpInt]
  cases cmpVal a b <;> simp

theorem compareTotalSame_cases (sign : Bool) (a b : Dec) :
    compareTotalSame sign a b = -1 ∨ compareTotalSame sign a b = 0 ∨ compareTotalSame sign a b = 1 := by
  unfold compareTotalSame
  cases sign <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> (repeat' split) <;> simp

theorem compareTotal_cases (a b : Dec) :
    compareTotal a b = -1 ∨ compareTotal a b = 0 ∨ compareTotal a b = 1 := by
  unfold compareTotal
  cases a.neg <;> cases b.neg <;> first | exact compareTotalSame_cases _ a b | simp

/-- `max` and `min` of non-NaN operands do not depend on the operand order, even
for numerically equal operands, where `compare_total` decides; the same holds for
`max_mag`, `min_mag`. When the values differ, `max` is `_fix` of the greater and `min`
of the lesser. A quiet NaN loses to a number. -/
def MinMaxCorrect : Prop :=
  ∀ (c : Ctx) (a b : Dec) (fl : List Signal),
    (nanKind a = 0 → nanKind b = 0 →
      (maxD c a b).run fl = (maxD c b a).run fl ∧ (minD c a b).run fl = (minD c b a).run fl ∧
      (maxMag c a b).run fl = (maxMag c b a).run fl ∧ (minMag c a b).run fl = (minMag c b a).run fl ∧
      (cmpVal a b = .gt → (maxD c a b).run fl = (fix c a).run fl ∧ (minD c a b).run fl = (fix c b).run fl)) ∧
    (nanKind a = 0 → nanKind b = 1 →
      (maxD c a b).run fl = (fix c a).run fl ∧ (minD c a b).run fl = (fix c a).run fl)

/-- Swapping the operands of a selection by an antisymmetric comparison. -/
theorem select_swap (cmp : Dec → Dec → Int) (lw : Bool) (a b : Dec)
    (hs : cmp b a = -cmp a b) (hc : cmp a b = -1 ∨ cmp a b = 0 ∨ cmp a b = 1) :
    (let cc := cmp a b
     let cc := if cc = 0 then compareTotal a b else cc
     if cc = -1 then (if lw then a else b) else (if lw then b else a)) =
    (let cc := cmp b a
     let cc := if cc = 0 then compareTotal b a else cc
     if cc = -1 then (if lw then b else a) else (if lw then a else b)) := by
  have ha := compareTotal_antisymm a b
  have hz := compareTotal_eq_zero a b
  have ht := compareTotal_cases a b
  simp only [hs]
  rcases hc with h | h | h <;> rw [h]
  · cases lw <;> simp
  · simp only [Int.neg_zero, ↓reduceIte, ha]
    rcases ht with h1 | h1 | h1 <;> rw [h1]
    · cases lw <;> simp
    · have := hz.mp h1
      subst this
      cases lw <;> simp
    · cases lw <;> simp
  · cases lw <;> simp

theorem magCmp_swap (a b : Dec) (ha : nanKind a = 0) (hb : nanKind b = 0) : magCmp b a = -magCmp a b := by
  have hk : ∀ d : Dec, nanKind d = 0 → nanKind (copyAbs d) = 0 := by
    intro d hd
    cases d with
    | nan n s p => cases s <;> simp [nanKind] at hd
    | _ => rfl
  exact cmpInt_swap _ _ (hk a ha) (hk b hb)

theorem minMaxCorrect_proven : MinMaxCorrect := by
  intro c a b fl
  constructor
  · intro ha hb
    have s1 := cmpInt_swap a b ha hb
    have s2 := magCmp_swap a b ha hb
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [maxD]
      rw [minmax_run _ _ c a b ha hb, minmax_run _ _ c b a hb ha, select_swap cmpInt false a b s1 (cmpInt_cases a b)]
    · simp only [minD]
      rw [minmax_run _ _ c a b ha hb, minmax_run _ _ c b a hb ha, select_swap cmpInt true a b s1 (cmpInt_cases a b)]
    · simp only [maxMag]
      rw [minmax_run _ _ c a b ha hb, minmax_run _ _ c b a hb ha, select_swap magCmp false a b s2 (cmpInt_cases _ _)]
    · simp only [minMag]
      rw [minmax_run _ _ c a b ha hb, minmax_run _ _ c b a hb ha, select_swap magCmp true a b s2 (cmpInt_cases _ _)]
    · intro hgt
      have h1 : cmpInt a b = 1 := by simp [cmpInt, hgt]
      constructor
      · simp only [maxD]
        rw [minmax_run _ _ c a b ha hb]
        simp [h1]
      · simp only [minD]
        rw [minmax_run _ _ c a b ha hb]
        simp [h1]
  · intro ha hb
    have hsp : isSpecial b = true := by
      cases b with
      | nan m s q => rfl
      | _ => simp [nanKind] at hb
    have hn : (minmaxNans c a b).run fl = (do let r ← fix c a; pure (some r) : DM (Option Dec)).run fl := by
      have h1 : isnan a = 0 := ha
      have h2 : isnan b = 1 := hb
      unfold minmaxNans
      simp [hsp, h1, h2]
    constructor
    · simp only [maxD, minmaxBy, StateT.run, bind, StateT.bind, Except.bind] at hn ⊢
      simp only [pure, StateT.pure, Except.pure, Except.bind] at hn ⊢
      rw [hn]
      cases fix c a fl with
      | error e => rfl
      | ok v => rfl
    · simp only [minD, minmaxBy, StateT.run, bind, StateT.bind, Except.bind] at hn ⊢
      simp only [pure, StateT.pure, Except.pure, Except.bind] at hn ⊢
      rw [hn]
      cases fix c a fl with
      | error e => rfl
      | ok v => rfl

end PyLean.Decimal
