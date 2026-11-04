import PyLean.Decimal.CmpProps
import PyLean.Decimal.Convert
import PyLean.Decimal.ContextProps

/-!
The comparison family pinned to the exact numeric order (`numOrder`, `CmpProps.lean`) and to
the documented NaN rules, for every operand kind `_convert_for_comparison` accepts.
-/

namespace PyLean.Decimal

open PyLean

/-! ## The NaN a comparison reports -/

/-- The operand the NaN checks pick: a signaling NaN first, the left one first, then a
quiet NaN, the left one first; quieted, with the payload cut to `prec - clamp` digits. -/
def nanPick (c : Ctx) (a b : Dec) : Dec :=
  if nanKind a = 2 then quietNaN c a else if nanKind b = 2 then quietNaN c b
  else if nanKind a = 1 then quietNaN c a else quietNaN c b

/-- `_ordInt`: the -1/0/1 `_cmp` returns for an ordering. -/
def ordInt : Ordering → Int
  | .lt => -1
  | .eq => 0
  | .gt => 1

theorem compareCheckNans_nan (c : Ctx) (a b : Dec) (h : nanKind a ≠ 0 ∨ nanKind b ≠ 0) :
    compareCheckNans c a b = (do raiseSig c .invalidOperation; pure (some (nanPick c a b))) := by
  rcases a with ⟨n1, c1, e1⟩ | n1 | ⟨n1, s1, p1⟩ <;> rcases b with ⟨n2, c2, e2⟩ | n2 | ⟨n2, s2, p2⟩ <;>
    (try cases s1) <;> (try cases s2) <;>
    simp_all [compareCheckNans, nanPick, quietOf_eq, isSpecial, isSnan, isQnan, isnan, nanKind]

theorem compareCheckNans_num (c : Ctx) (a b : Dec) (ha : nanKind a = 0) (hb : nanKind b = 0) :
    compareCheckNans c a b = pure none := by
  rcases a with ⟨n1, c1, e1⟩ | n1 | ⟨n1, s1, p1⟩ <;> rcases b with ⟨n2, c2, e2⟩ | n2 | ⟨n2, s2, p2⟩ <;>
    (try cases s1) <;> (try cases s2) <;> simp_all [compareCheckNans, isSpecial, isSnan, isQnan, isnan, nanKind]

/-- With a signaling NaN, `_check_nans` signals and returns `nanPick`. -/
theorem checkNans_snan (c : Ctx) (a b : Dec) (h : nanKind a = 2 ∨ nanKind b = 2) :
    checkNans c a (some b) = (do raiseSig c .invalidOperation; pure (some (nanPick c a b))) := by
  rcases a with ⟨n1, c1, e1⟩ | n1 | ⟨n1, s1, p1⟩ <;> rcases b with ⟨n2, c2, e2⟩ | n2 | ⟨n2, s2, p2⟩ <;>
    (try cases s1) <;> (try cases s2) <;> simp_all [checkNans, nanPick, quietNaN, fixNan_spec, nanKind]

/-- With quiet NaNs only, `_check_nans` returns `nanPick` and signals nothing. -/
theorem checkNans_qnan (c : Ctx) (a b : Dec) (h : nanKind a = 1 ∨ nanKind b = 1)
    (ha : nanKind a ≠ 2) (hb : nanKind b ≠ 2) : checkNans c a (some b) = pure (some (nanPick c a b)) := by
  rcases a with ⟨n1, c1, e1⟩ | n1 | ⟨n1, s1, p1⟩ <;> rcases b with ⟨n2, c2, e2⟩ | n2 | ⟨n2, s2, p2⟩ <;>
    (try cases s1) <;> (try cases s2) <;> simp_all [checkNans, nanPick, quietNaN, fixNan_spec, nanKind]

theorem checkNans_num (c : Ctx) (a b : Dec) (ha : nanKind a = 0) (hb : nanKind b = 0) :
    checkNans c a (some b) = pure none := by
  rcases a with ⟨n1, c1, e1⟩ | n1 | ⟨n1, s1, p1⟩ <;> rcases b with ⟨n2, c2, e2⟩ | n2 | ⟨n2, s2, p2⟩ <;>
    (try cases s1) <;> (try cases s2) <;> simp_all [checkNans, nanKind]

/-- `_compare_check_nans`, _pydecimal.py:822-853: any NaN signals InvalidOperation, and the
NaN returned is a signaling one before a quiet one, the left before the right. -/
def CompareCheckNansExact : Prop :=
  ∀ (c : Ctx) (a b : Dec) (fl : List Signal),
    (nanKind a ≠ 0 ∨ nanKind b ≠ 0 →
      (compareCheckNans c a b).run fl = afterSig c .invalidOperation fl (some (nanPick c a b))) ∧
    (nanKind a = 0 → nanKind b = 0 → (compareCheckNans c a b).run fl = .ok (none, fl))

theorem compareCheckNansExact_proven : CompareCheckNansExact := by
  intro c a b fl
  refine ⟨fun h => ?_, fun ha hb => ?_⟩
  · rw [compareCheckNans_nan c a b h]; exact raiseSig_then _ _ _ _
  · rw [compareCheckNans_num c a b ha hb]; rfl

/-! ## Rich comparisons and `compare` of two Decimals -/

/-- For two decimals: if neither is a NaN, `==`, `<`, `<=`, `>`, `>=` follow the exact numeric
order and set no flag, and `compare` and `compare_signal` return it as `Decimal(-1/0/1)`. If one
is a NaN, `==` is False and signals InvalidOperation only for a signaling NaN (False when that is
not trapped); the orderings and `compare_signal` signal InvalidOperation for every NaN; `<` etc.
are False; `compare` and `compare_signal` return the NaN `nanPick` chooses, and `compare` signals
only for a signaling NaN. (The comment at _pydecimal.py:909-924 and the decimal docs.) -/
def ComparisonsExact : Prop :=
  ∀ (c : Ctx) (a b : Dec) (fl : List Signal),
    (nanKind a = 0 → nanKind b = 0 →
      (richEq c a (.dec b)).run fl = .ok (some (decide (numOrder a b = .eq)), fl) ∧
      (richLt c a (.dec b)).run fl = .ok (some (decide (numOrder a b = .lt)), fl) ∧
      (richLe c a (.dec b)).run fl = .ok (some (decide (numOrder a b ≠ .gt)), fl) ∧
      (richGt c a (.dec b)).run fl = .ok (some (decide (numOrder a b = .gt)), fl) ∧
      (richGe c a (.dec b)).run fl = .ok (some (decide (numOrder a b ≠ .lt)), fl) ∧
      (compareD c a b).run fl = .ok (decOfInt (ordInt (numOrder a b)), fl) ∧
      (compareSignal c a b).run fl = .ok (decOfInt (ordInt (numOrder a b)), fl)) ∧
    (nanKind a ≠ 0 ∨ nanKind b ≠ 0 →
      (richEq c a (.dec b)).run fl =
        (if nanKind a = 2 ∨ nanKind b = 2 then afterSig c .invalidOperation fl (some false)
         else .ok (some false, fl)) ∧
      (richLt c a (.dec b)).run fl = afterSig c .invalidOperation fl (some false) ∧
      (richLe c a (.dec b)).run fl = afterSig c .invalidOperation fl (some false) ∧
      (richGt c a (.dec b)).run fl = afterSig c .invalidOperation fl (some false) ∧
      (richGe c a (.dec b)).run fl = afterSig c .invalidOperation fl (some false) ∧
      (compareD c a b).run fl =
        (if nanKind a = 2 ∨ nanKind b = 2 then afterSig c .invalidOperation fl (nanPick c a b)
         else .ok (nanPick c a b, fl)) ∧
      (compareSignal c a b).run fl = afterSig c .invalidOperation fl (nanPick c a b))

theorem cmpInt_numOrder (a b : Dec) (ha : nanKind a = 0) (hb : nanKind b = 0) :
    cmpInt a b = ordInt (numOrder a b) := by
  simp only [cmpInt, cmpVal_exact a b ha hb]
  cases numOrder a b <;> rfl

theorem isSpecial_of_nan {a : Dec} (h : nanKind a ≠ 0) : isSpecial a = true := by
  cases a with
  | nan n s p => rfl
  | _ => simp [nanKind] at h

theorem nanKind_cases (a : Dec) : nanKind a = 0 ∨ nanKind a = 1 ∨ nanKind a = 2 := by
  cases a with
  | nan n s p => cases s <;> simp [nanKind]
  | _ => simp [nanKind]

theorem comparisonsExact_proven : ComparisonsExact := by
  intro c a b fl
  refine ⟨fun ha hb => ?_, fun h => ?_⟩
  · have e := cmpInt_numOrder a b ha hb
    have hc : compareD c a b = pure (decOfInt (ordInt (numOrder a b))) := by
      unfold compareD
      rw [checkNans_num c a b ha hb, ← e]
      by_cases hs : (isSpecial a || isSpecial b) = true <;> simp [hs]
    refine ⟨?_, ?_, ?_, ?_, ?_, by rw [hc]; rfl, ?_⟩
    · have h' : richEq c a (.dec b) = pure (some (cmpInt a b == 0)) := by
        simp [richEq, convertForComparison, dunderEq, checkNans_num c a b ha hb]
      rw [h', e]; cases numOrder a b <;> rfl
    · have h' : richLt c a (.dec b) = pure (some (decide (cmpInt a b < 0))) := by
        simp [richLt, richOrd, convertForComparison, dunderOrd, compareCheckNans_num c a b ha hb]
      rw [h', e]; cases numOrder a b <;> rfl
    · have h' : richLe c a (.dec b) = pure (some (decide (cmpInt a b ≤ 0))) := by
        simp [richLe, richOrd, convertForComparison, dunderOrd, compareCheckNans_num c a b ha hb]
      rw [h', e]; cases numOrder a b <;> rfl
    · have h' : richGt c a (.dec b) = pure (some (decide (cmpInt a b > 0))) := by
        simp [richGt, richOrd, convertForComparison, dunderOrd, compareCheckNans_num c a b ha hb]
      rw [h', e]; cases numOrder a b <;> rfl
    · have h' : richGe c a (.dec b) = pure (some (decide (cmpInt a b ≥ 0))) := by
        simp [richGe, richOrd, convertForComparison, dunderOrd, compareCheckNans_num c a b ha hb]
      rw [h', e]; cases numOrder a b <;> rfl
    · simp only [compareSignal, compareCheckNans_num c a b ha hb, hc]; rfl
  · have hcc := compareCheckNans_nan c a b h
    have hsp : (isSpecial a || isSpecial b) = true := by
      rcases h with h | h <;> simp [isSpecial_of_nan h]
    have hord : ∀ t : Int → Bool, (richOrd t c a (.dec b)).run fl = afterSig c .invalidOperation fl (some false) := by
      intro t
      have h' : richOrd t c a (.dec b) = (do raiseSig c .invalidOperation; pure (some false)) := by
        simp [richOrd, convertForComparison, dunderOrd, hcc]
      rw [h']; exact raiseSig_then _ _ _ _
    refine ⟨?_, hord _, hord _, hord _, hord _, ?_, ?_⟩
    · by_cases hs : nanKind a = 2 ∨ nanKind b = 2
      · rw [if_pos hs]
        have h' : richEq c a (.dec b) = (do raiseSig c .invalidOperation; pure (some false)) := by
          simp [richEq, convertForComparison, dunderEq, checkNans_snan c a b hs]
        rw [h']; exact raiseSig_then _ _ _ _
      · rw [if_neg hs]
        have hq : nanKind a = 1 ∨ nanKind b = 1 := by
          rcases nanKind_cases a with h1 | h1 | h1 <;> rcases nanKind_cases b with h2 | h2 | h2 <;> omega
        have h' : richEq c a (.dec b) = pure (some false) := by
          simp [richEq, convertForComparison, dunderEq,
            checkNans_qnan c a b hq (fun h' => hs (Or.inl h')) (fun h' => hs (Or.inr h'))]
        rw [h']; rfl
    · by_cases hs : nanKind a = 2 ∨ nanKind b = 2
      · rw [if_pos hs]
        have h' : compareD c a b = (do raiseSig c .invalidOperation; pure (nanPick c a b)) := by
          simp [compareD, hsp, checkNans_snan c a b hs]
        rw [h']; exact raiseSig_then _ _ _ _
      · rw [if_neg hs]
        have hq : nanKind a = 1 ∨ nanKind b = 1 := by
          rcases nanKind_cases a with h1 | h1 | h1 <;> rcases nanKind_cases b with h2 | h2 | h2 <;> omega
        have h' : compareD c a b = pure (nanPick c a b) := by
          simp [compareD, hsp,
            checkNans_qnan c a b hq (fun h' => hs (Or.inl h')) (fun h' => hs (Or.inr h'))]
        rw [h']; rfl
    · have h' : compareSignal c a b = (do raiseSig c .invalidOperation; pure (nanPick c a b)) := by
        simp [compareSignal, hcc]
      rw [h']; exact raiseSig_then _ _ _ _

/-! ## `max`, `min`, `max_mag`, `min_mag` -/

theorem nanKind_copyAbs (a : Dec) : nanKind (copyAbs a) = nanKind a := by
  cases a with
  | nan n s p => cases s <;> rfl
  | _ => rfl

theorem minmaxNans_nan (c : Ctx) (a b : Dec) (h : nanKind a = 2 ∨ nanKind b = 2 ∨ (nanKind a = 1 ∧ nanKind b = 1)) :
    minmaxNans c a b = (do let r ← checkNans c a (some b); pure r) := by
  rcases a with ⟨n1, c1, e1⟩ | n1 | ⟨n1, s1, p1⟩ <;> rcases b with ⟨n2, c2, e2⟩ | n2 | ⟨n2, s2, p2⟩ <;>
    (try cases s1) <;> (try cases s2) <;> simp_all [minmaxNans, isSpecial, isnan, nanKind]

/-- The NaN outcome of `max` and friends: `_check_nans`, which signals for a signaling NaN. -/
def nanOutcome (c : Ctx) (a b : Dec) (fl : List Signal) : Py (Dec × List Signal) :=
  if nanKind a = 2 ∨ nanKind b = 2 then afterSig c .invalidOperation fl (nanPick c a b)
  else .ok (nanPick c a b, fl)

theorem minmaxBy_nan (cmp : Dec → Dec → Int) (lw : Bool) (c : Ctx) (a b : Dec) (fl : List Signal)
    (h : nanKind a = 2 ∨ nanKind b = 2 ∨ (nanKind a = 1 ∧ nanKind b = 1)) :
    (minmaxBy cmp lw c a b).run fl = nanOutcome c a b fl := by
  unfold nanOutcome
  by_cases hs : nanKind a = 2 ∨ nanKind b = 2
  · rw [if_pos hs]
    have h' : minmaxBy cmp lw c a b = (do raiseSig c .invalidOperation; pure (nanPick c a b)) := by
      simp [minmaxBy, minmaxNans_nan c a b h, checkNans_snan c a b hs]
    rw [h']; exact raiseSig_then _ _ _ _
  · rw [if_neg hs]
    have hq : nanKind a = 1 ∨ nanKind b = 1 := by omega
    have h' : minmaxBy cmp lw c a b = pure (nanPick c a b) := by
      simp [minmaxBy, minmaxNans_nan c a b h,
        checkNans_qnan c a b hq (fun h' => hs (Or.inl h')) (fun h' => hs (Or.inr h'))]
    rw [h']; rfl

theorem minmaxBy_qnan_left (cmp : Dec → Dec → Int) (lw : Bool) (c : Ctx) (a b : Dec) (fl : List Signal)
    (ha : nanKind a = 1) (hb : nanKind b = 0) : (minmaxBy cmp lw c a b).run fl = (fix c b).run fl := by
  have h' : minmaxBy cmp lw c a b = fix c b := by
    rcases a with ⟨n1, c1, e1⟩ | n1 | ⟨n1, s1, p1⟩ <;> rcases b with ⟨n2, c2, e2⟩ | n2 | ⟨n2, s2, p2⟩ <;>
      (try cases s1) <;> (try cases s2) <;> simp_all [minmaxBy, minmaxNans, isSpecial, isnan, nanKind]
  rw [h']

theorem minmaxBy_qnan_right (cmp : Dec → Dec → Int) (lw : Bool) (c : Ctx) (a b : Dec) (fl : List Signal)
    (ha : nanKind a = 0) (hb : nanKind b = 1) : (minmaxBy cmp lw c a b).run fl = (fix c a).run fl := by
  have h' : minmaxBy cmp lw c a b = fix c a := by
    rcases a with ⟨n1, c1, e1⟩ | n1 | ⟨n1, s1, p1⟩ <;> rcases b with ⟨n2, c2, e2⟩ | n2 | ⟨n2, s2, p2⟩ <;>
      (try cases s1) <;> (try cases s2) <;> simp_all [minmaxBy, minmaxNans, isSpecial, isnan, nanKind]
  rw [h']

/-- Which operand `max` keeps for numbers: the greater value, and for equal values the one
`compare_total` puts higher (_pydecimal.py:2903-2918). `min` keeps the other. -/
def maxPick (o : Ordering) (ct : Int) (a b : Dec) : Dec :=
  match o with
  | .gt => a
  | .lt => b
  | .eq => if ct = -1 then b else a

def minPick (o : Ordering) (ct : Int) (a b : Dec) : Dec :=
  match o with
  | .lt => a
  | .gt => b
  | .eq => if ct = -1 then a else b

/-- `max`, `min` (_pydecimal.py:2880-2954) and `max_mag`, `min_mag` (:3515-3573): for two
numbers, `_fix` of the operand the exact order picks (of the magnitudes for `*_mag`), ties
broken by `compare_total` on the operands themselves; a quiet NaN against a number gives `_fix`
of the number; otherwise (a signaling NaN, or two quiet NaNs) the `_check_nans` result. -/
def MinMaxExact : Prop :=
  ∀ (c : Ctx) (a b : Dec) (fl : List Signal),
    (nanKind a = 0 → nanKind b = 0 →
      (maxD c a b).run fl = (fix c (maxPick (numOrder a b) (compareTotal a b) a b)).run fl ∧
      (minD c a b).run fl = (fix c (minPick (numOrder a b) (compareTotal a b) a b)).run fl ∧
      (maxMag c a b).run fl =
        (fix c (maxPick (numOrder (copyAbs a) (copyAbs b)) (compareTotal a b) a b)).run fl ∧
      (minMag c a b).run fl =
        (fix c (minPick (numOrder (copyAbs a) (copyAbs b)) (compareTotal a b) a b)).run fl) ∧
    (nanKind a = 1 → nanKind b = 0 →
      (maxD c a b).run fl = (fix c b).run fl ∧ (minD c a b).run fl = (fix c b).run fl ∧
      (maxMag c a b).run fl = (fix c b).run fl ∧ (minMag c a b).run fl = (fix c b).run fl) ∧
    (nanKind a = 0 → nanKind b = 1 →
      (maxD c a b).run fl = (fix c a).run fl ∧ (minD c a b).run fl = (fix c a).run fl ∧
      (maxMag c a b).run fl = (fix c a).run fl ∧ (minMag c a b).run fl = (fix c a).run fl) ∧
    (nanKind a = 2 ∨ nanKind b = 2 ∨ (nanKind a = 1 ∧ nanKind b = 1) →
      (maxD c a b).run fl = nanOutcome c a b fl ∧ (minD c a b).run fl = nanOutcome c a b fl ∧
      (maxMag c a b).run fl = nanOutcome c a b fl ∧ (minMag c a b).run fl = nanOutcome c a b fl)

theorem select_pick (o : Ordering) (ct : Int) (a b : Dec) :
    (let cc := ordInt o
     let cc := if cc = 0 then ct else cc
     if cc = -1 then (if false then a else b) else (if false then b else a)) = maxPick o ct a b ∧
    (let cc := ordInt o
     let cc := if cc = 0 then ct else cc
     if cc = -1 then (if true then a else b) else (if true then b else a)) = minPick o ct a b := by
  cases o <;> simp [ordInt, maxPick, minPick]

theorem minMaxExact_proven : MinMaxExact := by
  intro c a b fl
  refine ⟨fun ha hb => ?_, fun ha hb => ?_, fun ha hb => ?_, fun h => ?_⟩
  · have e1 := cmpInt_numOrder a b ha hb
    have e2 : magCmp a b = ordInt (numOrder (copyAbs a) (copyAbs b)) :=
      cmpInt_numOrder _ _ (by rw [nanKind_copyAbs]; exact ha) (by rw [nanKind_copyAbs]; exact hb)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [maxD]; rw [minmax_run _ _ c a b ha hb, e1, (select_pick _ _ a b).1]
    · simp only [minD]; rw [minmax_run _ _ c a b ha hb, e1, (select_pick _ _ a b).2]
    · simp only [maxMag]; rw [minmax_run _ _ c a b ha hb, e2, (select_pick _ _ a b).1]
    · simp only [minMag]; rw [minmax_run _ _ c a b ha hb, e2, (select_pick _ _ a b).2]
  · exact ⟨minmaxBy_qnan_left _ _ c a b fl ha hb, minmaxBy_qnan_left _ _ c a b fl ha hb,
      minmaxBy_qnan_left _ _ c a b fl ha hb, minmaxBy_qnan_left _ _ c a b fl ha hb⟩
  · exact ⟨minmaxBy_qnan_right _ _ c a b fl ha hb, minmaxBy_qnan_right _ _ c a b fl ha hb,
      minmaxBy_qnan_right _ _ c a b fl ha hb, minmaxBy_qnan_right _ _ c a b fl ha hb⟩
  · exact ⟨minmaxBy_nan _ _ c a b fl h, minmaxBy_nan _ _ c a b fl h, minmaxBy_nan _ _ c a b fl h,
      minmaxBy_nan _ _ c a b fl h⟩

/-! ## `compare_total`, `compare_total_mag` -/

/-- `compare_total` (_pydecimal.py:2999-3069) is the total order of the specification
(General Decimal Arithmetic, "compare-total"; decimal docs: `Decimal('12.0').compare_total(
Decimal('12'))` is -1): it is antisymmetric and 0 only for identical representations; for
numbers of different value it is the numeric order; equal values with different signs put the
negative first; equal values with the same sign are ordered by exponent, the lower exponent
first when positive and last when negative; a positive NaN is above every number and a negative
one below, a signaling NaN is between the numbers and the quiet NaNs, and NaNs of one kind and
sign are ordered by payload. `compare_total_mag` is the same order of the magnitudes. -/
def CompareTotalExact : Prop :=
  (∀ a b : Dec, compareTotal b a = -compareTotal a b ∧ (compareTotal a b = 0 ↔ a = b)) ∧
  (∀ a b : Dec, nanKind a = 0 → nanKind b = 0 → numOrder a b ≠ .eq →
    compareTotal a b = ordInt (numOrder a b)) ∧
  (∀ a b : Dec, nanKind a = 0 → nanKind b = 0 → numOrder (copyAbs a) (copyAbs b) ≠ .eq →
    compareTotalMag a b = ordInt (numOrder (copyAbs a) (copyAbs b))) ∧
  (∀ a b : Dec, nanKind a = 0 → nanKind b = 0 → numOrder a b = .eq → a.neg ≠ b.neg →
    compareTotal a b = if a.neg then -1 else 1) ∧
  (∀ (n : Bool) (c1 c2 : Nat) (e1 e2 : Int), numOrder (.fin n c1 e1) (.fin n c2 e2) = .eq → e1 < e2 →
    compareTotal (.fin n c1 e1) (.fin n c2 e2) = if n then 1 else -1) ∧
  (∀ (x : Dec) (s : Bool) (p : Nat), nanKind x = 0 →
    compareTotal (.nan false s p) x = 1 ∧ compareTotal (.nan true s p) x = -1 ∧
    compareTotalMag (.nan true s p) x = 1) ∧
  (∀ p q : Nat, compareTotal (.nan false true p) (.nan false false q) = -1 ∧
    compareTotal (.nan true true p) (.nan true false q) = 1) ∧
  (∀ (n s : Bool) (p q : Nat), p < q → compareTotal (.nan n s p) (.nan n s q) = if n then 1 else -1)

theorem compareTotal_num (a b : Dec) (ha : nanKind a = 0) (hb : nanKind b = 0) (h : numOrder a b ≠ .eq) :
    compareTotal a b = ordInt (numOrder a b) := by
  have hc := cmpVal_exact a b ha hb
  rcases a with ⟨n1, c1, e1⟩ | n1 | ⟨n1, s1, p1⟩ <;> rcases b with ⟨n2, c2, e2⟩ | n2 | ⟨n2, s2, p2⟩ <;>
    (try cases s1) <;> (try cases s2) <;> (try simp [nanKind] at ha hb)
  all_goals
    cases n1 <;> cases n2 <;>
    simp only [compareTotal, compareTotalSame, Dec.neg, nanKind, ne_eq, not_true_eq_false, or_self,
      ↓reduceIte, hc, Bool.false_eq_true] <;>
    (try (revert h hc; generalize numOrder _ _ = o; intro h hc; cases o <;> simp_all [ordInt]))
  all_goals (simp only [cmpVal, signOrd, Ordering.swap] at hc; (repeat' split at hc) <;> simp_all)

theorem compareTotalExact_proven : CompareTotalExact := by
  refine ⟨fun a b => ⟨compareTotal_antisymm a b, compareTotal_eq_zero a b⟩,
    fun a b ha hb h => compareTotal_num a b ha hb h,
    fun a b ha hb h => compareTotal_num _ _ (by rw [nanKind_copyAbs]; exact ha) (by rw [nanKind_copyAbs]; exact hb) h,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro a b ha hb _ hs
    rcases a with ⟨n1, c1, e1⟩ | n1 | ⟨n1, s1, p1⟩ <;> rcases b with ⟨n2, c2, e2⟩ | n2 | ⟨n2, s2, p2⟩ <;>
      (try cases s1) <;> (try cases s2) <;> (try simp [nanKind] at ha hb) <;>
      cases n1 <;> cases n2 <;> simp_all [compareTotal, Dec.neg]
  · intro n c1 c2 e1 e2 h he
    have hc := cmpVal_exact (.fin n c1 e1) (.fin n c2 e2) rfl rfl
    rw [h] at hc
    cases n <;> simp [compareTotal, compareTotalSame, Dec.neg, nanKind, hc, expOf, he]
  · intro x s p hx
    rcases x with ⟨n2, c2, e2⟩ | n2 | ⟨n2, s2, p2⟩ <;> (try cases s2) <;> (try simp [nanKind] at hx) <;>
      cases s <;> (try cases n2) <;>
      simp [compareTotal, compareTotalMag, compareTotalSame, copyAbs, Dec.withSign, Dec.neg, nanKind]
  · intro p q
    simp [compareTotal, compareTotalSame, Dec.neg, nanKind]
  · intro n s p q h
    cases n <;> cases s <;> simp [compareTotal, compareTotalSame, Dec.neg, nanKind, payloadOf, h]

/-! ## Classification -/

/-- `number_class` (_pydecimal.py:3667-3707) gives all ten classes of the docs by sign, kind,
zero coefficient and the threshold `adjusted() < Emin`; `is_normal` and `is_subnormal`
(:3200-3226) test that threshold on non-zero finite values and are False otherwise; `is_zero`
(:3228-3230) and `__bool__` (:855-860) test the coefficient, NaNs and infinities being nonzero;
`_isinfinity` (:777-788) is +1 / -1 by sign. -/
def ClassificationExact : Prop :=
  ∀ (c : Ctx) (d : Dec),
    numberClass c d = (match d with
      | .nan _ true _ => "sNaN"
      | .nan _ false _ => "NaN"
      | .inf n => if n then "-Infinity" else "+Infinity"
      | .fin n co e =>
        if co = 0 then (if n then "-Zero" else "+Zero")
        else if adjustedD co e < c.emin then (if n then "-Subnormal" else "+Subnormal")
        else if n then "-Normal" else "+Normal") ∧
    isNormal c d = (match d with | .fin _ co e => decide (co ≠ 0 ∧ c.emin ≤ adjustedD co e) | _ => false) ∧
    isSubnormal c d = (match d with | .fin _ co e => decide (co ≠ 0 ∧ adjustedD co e < c.emin) | _ => false) ∧
    isZero d = (match d with | .fin _ co _ => decide (co = 0) | _ => false) ∧
    decBool d = (match d with | .fin _ co _ => decide (co ≠ 0) | _ => true) ∧
    isinfinity d = (match d with | .inf n => if n then -1 else 1 | _ => 0)

theorem classificationExact_proven : ClassificationExact := by
  intro c d
  rcases d with ⟨n, co, e⟩ | n | ⟨n, s, p⟩
  · by_cases hc : co = 0
    · subst hc
      cases n <;> simp [numberClass, isSnan, isQnan, isnan, nanKind, isinfinity, isZero, isNormal,
        isSubnormal, isSpecial, decBool, Dec.neg]
    · have hz : isZero (.fin n co e) = false := by cases co <;> simp_all [isZero]
      by_cases ha : adjustedD co e < c.emin
      · have ha' : ¬ c.emin ≤ adjustedD co e := by omega
        cases n <;> simp [numberClass, isSnan, isQnan, isnan, nanKind, isinfinity, hz, hc, isNormal,
          isSubnormal, isSpecial, decBool, Dec.adjusted, Dec.neg, ha, ha']
      · have ha' : c.emin ≤ adjustedD co e := by omega
        cases n <;> simp [numberClass, isSnan, isQnan, isnan, nanKind, isinfinity, hz, hc, isNormal,
          isSubnormal, isSpecial, decBool, Dec.adjusted, Dec.neg, ha, ha']
  · cases n <;> simp [numberClass, isSnan, isQnan, isnan, nanKind, isinfinity, isZero, isNormal,
      isSubnormal, isSpecial, decBool]
  · cases s <;> simp [numberClass, isSnan, isQnan, isnan, nanKind, isinfinity, isZero, isNormal,
      isSubnormal, isSpecial, decBool]

/-! ## `copy_abs`, `copy_negate` -/

/-- `copy_negate` (_pydecimal.py:3088-3093) flips the sign and keeps the coefficient, exponent,
NaN kind and payload: it is an involution that reverses the numeric order. `copy_abs`
(:3084-3086) is `copy_negate` on a negative operand and the operand itself otherwise, so
`copy_sign(copy_abs(a), a)` rebuilds `a`. -/
def CopyExact : Prop :=
  ∀ a b : Dec,
    copyAbs a = (if a.neg then copyNegate a else a) ∧ (copyAbs a).neg = false ∧
    copySign (copyAbs a) a = a ∧
    (copyNegate a).neg = !a.neg ∧ copyNegate (copyNegate a) = a ∧
    nanKind (copyNegate a) = nanKind a ∧ payloadOf (copyNegate a) = payloadOf a ∧
    expOf (copyNegate a) = expOf a ∧
    (nanKind a = 0 → nanKind b = 0 → numOrder (copyNegate a) (copyNegate b) = (numOrder a b).swap)

theorem finOrder_neg (n1 n2 : Bool) (c1 c2 : Nat) (e1 e2 : Int) :
    finOrder (!n1) c1 e1 (!n2) c2 e2 = (finOrder n1 c1 e1 n2 c2 e2).swap := by
  simp only [finOrder, ordOf, sgnVal]
  generalize c1 * 10 ^ (e1 - min e1 e2).toNat = P1
  generalize c2 * 10 ^ (e2 - min e1 e2).toNat = P2
  cases n1 <;> cases n2 <;> simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] <;>
    (repeat' split) <;> simp_all [Ordering.swap] <;> omega

theorem copyExact_proven : CopyExact := by
  intro a b
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun ha hb => ?_⟩
  · rcases a with ⟨n, co, e⟩ | n | ⟨n, s, p⟩ <;> cases n <;>
      simp [copyAbs, copyNegate, negate, Dec.withSign, Dec.neg]
  · rcases a with ⟨n, co, e⟩ | n | ⟨n, s, p⟩ <;> rfl
  · rcases a with ⟨n, co, e⟩ | n | ⟨n, s, p⟩ <;> rfl
  · rcases a with ⟨n, co, e⟩ | n | ⟨n, s, p⟩ <;> rfl
  · rcases a with ⟨n, co, e⟩ | n | ⟨n, s, p⟩ <;> simp [copyNegate, negate, Dec.withSign, Dec.neg]
  · rcases a with ⟨n, co, e⟩ | n | ⟨n, s, p⟩ <;> (try cases s) <;> rfl
  · rcases a with ⟨n, co, e⟩ | n | ⟨n, s, p⟩ <;> rfl
  · rcases a with ⟨n, co, e⟩ | n | ⟨n, s, p⟩ <;> rfl
  · rcases a with ⟨n1, c1, e1⟩ | n1 | ⟨n1, s1, p1⟩ <;> rcases b with ⟨n2, c2, e2⟩ | n2 | ⟨n2, s2, p2⟩ <;>
      (try cases s1) <;> (try cases s2) <;> (try simp [nanKind] at ha hb)
    · exact finOrder_neg n1 n2 c1 c2 e1 e2
    all_goals cases n1 <;> (try cases n2) <;> rfl

/-! ## `Overflow.handle`, `InvalidOperation.handle`, `_fix_nan` -/

theorem numDigits_nines {p : Nat} (hp : 1 ≤ p) : numDigits (10 ^ p - 1) = p := by
  have h1 : 10 ^ p - 1 < 10 ^ p := Nat.sub_lt (Nat.pow_pos (by decide)) (by decide)
  have hle := (numDigits_le_iff (by omega : 0 < p)).mpr h1
  have hge : ¬ numDigits (10 ^ p - 1) ≤ p - 1 := by
    intro h
    by_cases hp1 : p - 1 = 0
    · have : p = 1 := by omega
      subst this; simp [numDigits] at h
    · have := (numDigits_le_iff (by omega : 0 < p - 1)).mp h
      have h2 : 10 ^ p = 10 * 10 ^ (p - 1) := by
        rw [← Nat.pow_succ']; congr 1; omega
      have h3 : 1 ≤ 10 ^ (p - 1) := Nat.one_le_pow _ _ (by decide)
      omega
  omega

/-- `Overflow.handle` (_pydecimal.py:284-297) against its docstring (:267-282): an infinity
with the result's sign for ROUND_HALF_UP, HALF_EVEN, HALF_DOWN and UP; for ROUND_DOWN the
largest finite number of the precision, `prec` nines at exponent `Emax - prec + 1` (adjusted
exponent Emax), with the result's sign; ROUND_CEILING gives that for a negative result and
+Infinity otherwise, ROUND_FLOOR that for a positive result and -Infinity otherwise.
ROUND_05UP, which the docstring does not list, gives the ROUND_DOWN value (rounding nines
toward zero leaves them). `_fix`'s overflow branches return the same value. -/
def OverflowHandleTable : Prop :=
  ∀ (c : Ctx) (s : Bool),
    handle c (.overflow s) = some (match c.rounding with
      | .halfUp | .halfEven | .halfDown | .up => .inf s
      | .down | .r05up => .fin s (10 ^ c.prec - 1) (c.emax - c.prec + 1)
      | .ceiling => if s then .fin s (10 ^ c.prec - 1) (c.emax - c.prec + 1) else .inf false
      | .floor => if s then .inf true else .fin s (10 ^ c.prec - 1) (c.emax - c.prec + 1)) ∧
    (1 ≤ c.prec → numDigits (10 ^ c.prec - 1) = c.prec ∧
      adjustedD (10 ^ c.prec - 1) (c.emax - c.prec + 1) = c.emax)

theorem overflowHandleTable_proven : OverflowHandleTable := by
  intro c s
  refine ⟨?_, fun hp => ⟨numDigits_nines hp, ?_⟩⟩
  · simp only [handle, overflowResult]
    cases c.rounding <;> cases s <;> rfl
  · simp only [adjustedD, numDigits_nines hp]; omega

/-- `_fix_nan` (_pydecimal.py:1701-1711) keeps the sign and kind and the last `prec - clamp`
payload digits; `InvalidOperation.handle` (:158-162) returns that, quiet, for the NaN
operand it is given, and the positive quiet NaN `_NaN` without one. -/
def FixNanExact : Prop :=
  ∀ (c : Ctx) (n s : Bool) (p : Nat),
    fixNan c n s p = .nan n s (p % 10 ^ nanDigits c) ∧
    handle c (.invalidOperation (some (.nan n s p))) = some (.nan n false (p % 10 ^ nanDigits c)) ∧
    handle c (.invalidOperation none) = some (.nan false false 0)

theorem fixNanExact_proven : FixNanExact := by
  intro c n s p
  exact ⟨fixNan_spec c n s p, by simp [handle, quietOf, fixNan_spec], rfl⟩

/-! ## `__int__` -/

/-- `int(d)` (`__int__`, _pydecimal.py:1672-1683) truncates toward zero, as `_decimal` does
(`cToInt .down`, pinned by `IntConversionsC`): `int(self._int) * 10**exp` for `exp >= 0` and
`int(self._int[:exp] or '0')` otherwise. The int/str limit raises ValueError exactly when that
digit string is longer than 4300: the coefficient for `exp >= 0`, its integer part (at least one
digit) otherwise. NaN gives ValueError, an infinity OverflowError. -/
def IntTruncExact : Prop :=
  ∀ (neg : Bool) (c : Nat) (e : Int),
    let mag := if e ≥ 0 then c * 10 ^ e.toNat else c / 10 ^ e.natAbs
    let digits : Nat := if e ≥ 0 then numDigits c else max 1 ((numDigits c : Int) + e).toNat
    (digits ≤ maxStrDigits →
      pyInt (.fin neg c e) = .ok (if neg then -(mag : Int) else mag) ∧
      cToInt .down (.fin neg c e) = pyInt (.fin neg c e)) ∧
    (maxStrDigits < digits → ∃ msg, pyInt (.fin neg c e) = .error (.valueError msg)) ∧
    (∀ s p, pyInt (.nan neg s p) = .error (.valueError "Cannot convert NaN to integer")) ∧
    pyInt (.inf neg) = .error (.overflowError "Cannot convert infinity to integer")

theorem intTruncExact_proven : IntTruncExact := by
  intro neg c e mag digits
  refine ⟨fun hd => ?_, fun hd => ?_, fun s p => rfl, rfl⟩
  · by_cases he : e ≥ 0
    · have hl : ¬ numDigits c > maxStrDigits := by simp only [digits, if_pos he] at hd; omega
      simp [pyInt, he, intLimit, hl, mag, truncDiv, cToInt, roundToIntExact, bind, Except.bind, pure,
        Except.pure]
    · have hl : ¬ (if (numDigits c : Int) + e ≤ 0 then 1 else ((numDigits c : Int) + e).toNat) > maxStrDigits := by
        simp only [digits, if_neg he] at hd; split <;> omega
      have hr : ∀ r : Nat, ¬ ((if r = 0 then (0 : Int) else -1) = 1) := by intro r; split <;> omega
      simp only [pyInt, he, ↓reduceIte, intLimit, hl, mag, cToInt, roundToIntExact, roundDir, hr]
      simp [bind, Except.bind, pure, Except.pure, truncDiv, Int.natCast_ediv, Int.natCast_pow]
  · by_cases he : e ≥ 0
    · have hl : numDigits c > maxStrDigits := by simp only [digits, if_pos he] at hd; omega
      exact ⟨limitToIntMsg (numDigits c), by simp [pyInt, he, intLimit, hl, bind, Except.bind]⟩
    · have hl : (if (numDigits c : Int) + e ≤ 0 then 1 else ((numDigits c : Int) + e).toNat) > maxStrDigits := by
        simp only [digits, if_neg he] at hd; split <;> omega
      exact ⟨limitToIntMsg (if (numDigits c : Int) + e ≤ 0 then 1 else ((numDigits c : Int) + e).toNat),
        by simp [pyInt, he, intLimit, hl, bind, Except.bind]⟩

/-! ## Comparisons with ints, Fractions, floats, complex numbers and other objects -/

/-- `self` as `_convert_for_comparison` rescales it for a Rational with denominator `d`. -/
def scaleBy (a : Dec) (d : Nat) : Dec :=
  match a with
  | .fin s co e => .fin s (co * d) e
  | x => x

/-- The digit limits `_convert_for_comparison` meets for a Rational `n / d`:
`int(self._int)`, `str(... * d)` and `Decimal(n)`. -/
def RatLimitsOk (a : Dec) (n : Int) (d : Nat) : Prop :=
  (match a with
   | .fin _ co _ => numDigits co ≤ maxStrDigits ∧ numDigits (co * d) ≤ maxStrDigits
   | _ => True) ∧ numDigits n.natAbs ≤ maxStrDigits

theorem liftPy_pure {α : Type} {x : Py α} {v : α} (h : x = .ok v) : liftPy x = pure v := by
  subst h; rfl

theorem run_setFlag_bind {β : Type} (s : Signal) (f : Unit → DM β) (fl : List Signal) :
    (setFlag s >>= f).run fl = (f ()).run (addFlag s fl) := rfl

theorem run_raiseSig_bind {β : Type} (c : Ctx) (s : Signal) (f : Unit → DM β) (fl : List Signal) :
    (raiseSig c s >>= f).run fl =
      if s ∈ c.traps then .error (.named s.name "~") else (f ()).run (addFlag s fl) := by
  unfold addFlag
  by_cases h : s ∈ c.traps <;>
    simp [raiseSig, h, StateT.run, bind, StateT.bind, Except.bind, modify, modifyGet,
      MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw, StateT.lift]

/-- `_convert_for_comparison` (_pydecimal.py:6115-6149) with the rich comparisons: against a
Rational `n / d` (an int has `d = 1`; `d > 0` is `numbers.Rational`'s invariant) the result is
the comparison of `self * d` with `Decimal(n)`, so for a finite `self = ±co·10^e` it is the
exact order of `±co·d·10^e` and `n`, which is the order of `self` and `n / d`; past the
4300-digit limit it raises ValueError. A float is compared as `Decimal.from_float(f)` after
FloatOperation, which `==` only flags and the orderings signal (raising when trapped). A complex
with zero imaginary part compares under `==` as its real part; any other complex, and any other
object, gives NotImplemented with no flag. -/
def ConvertComparisonsCorrect : Prop :=
  ∀ (c : Ctx) (a : Dec) (fl : List Signal),
    (∀ n d, RatLimitsOk a n d →
      richEq c a (.rat n d) = richEq c (scaleBy a d) (.dec (.fin (decide (n < 0)) n.natAbs 0)) ∧
      ∀ t, richOrd t c a (.rat n d) = richOrd t c (scaleBy a d) (.dec (.fin (decide (n < 0)) n.natAbs 0))) ∧
    (∀ (s : Bool) (co : Nat) (e : Int) (n : Int) (d : Nat), a = .fin s co e → RatLimitsOk a n d →
      (richEq c a (.rat n d)).run fl =
        .ok (some (decide (finOrder s (co * d) e (decide (n < 0)) n.natAbs 0 = .eq)), fl) ∧
      (richLt c a (.rat n d)).run fl =
        .ok (some (decide (finOrder s (co * d) e (decide (n < 0)) n.natAbs 0 = .lt)), fl)) ∧
    (∀ n d, ¬ RatLimitsOk a n d →
      (∃ msg, (richEq c a (.rat n d)).run fl = .error (.valueError msg)) ∧
      ∀ t, ∃ msg, (richOrd t c a (.rat n d)).run fl = .error (.valueError msg)) ∧
    (∀ f x, fromFloat f = .ok x →
      (richEq c a (.float f)).run fl = (richEq c a (.dec x)).run (addFlag .floatOperation fl) ∧
      ∀ t, (richOrd t c a (.float f)).run fl =
        if Signal.floatOperation ∈ c.traps then .error (.named "FloatOperation" "~")
        else (richOrd t c a (.dec x)).run (addFlag .floatOperation fl)) ∧
    (∀ re im, richEq c a (.complex re im) =
      if Binary64.F64.eq im (Binary64.F64.zero false) then richEq c a (.float re) else pure none) ∧
    (∀ t re im, richOrd t c a (.complex re im) = pure none) ∧
    richEq c a .other = pure none ∧ (∀ t, richOrd t c a .other = pure none)

theorem convert_rat (c : Ctx) (eqOp : Bool) (a : Dec) (n : Int) (d : Nat) (h : RatLimitsOk a n d) :
    convertForComparison c eqOp a (.rat n d) = pure (some (scaleBy a d, .fin (decide (n < 0)) n.natAbs 0)) := by
  obtain ⟨ha, hn⟩ := h
  have hb : pyFromInt n = .ok (.fin (decide (n < 0)) n.natAbs 0) := by
    simp [pyFromInt, strLimit, show ¬ numDigits n.natAbs > maxStrDigits by omega, bind, Except.bind,
      pure, Except.pure]
  rcases a with ⟨s, co, e⟩ | s | ⟨s, t, p⟩
  · obtain ⟨h1, h2⟩ := ha
    have e1 : intLimit (numDigits co) = .ok () := by simp [intLimit, show ¬ numDigits co > maxStrDigits by omega]
    have e2 : strLimit (co * d) = .ok () := by simp [strLimit, show ¬ numDigits (co * d) > maxStrDigits by omega]
    simp [convertForComparison, liftPy_pure e1, liftPy_pure e2, liftPy_pure hb, scaleBy]
  · simp [convertForComparison, liftPy_pure hb, scaleBy]
  · simp [convertForComparison, liftPy_pure hb, scaleBy]

theorem convert_dec (c : Ctx) (eqOp : Bool) (a d : Dec) :
    convertForComparison c eqOp a (.dec d) = pure (some (a, d)) := rfl

theorem convertComparisonsCorrect_proven : ConvertComparisonsCorrect := by
  intro c a fl
  refine ⟨fun n d h => ⟨?_, fun t => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [richEq, convert_rat c true a n d h, convert_dec]
  · simp [richOrd, convert_rat c false a n d h, convert_dec]
  · intro s co e n d ha h
    have h1 : richEq c a (.rat n d) = richEq c (scaleBy a d) (.dec (.fin (decide (n < 0)) n.natAbs 0)) := by
      simp [richEq, convert_rat c true a n d h, convert_dec]
    have h2 : richLt c a (.rat n d) = richLt c (scaleBy a d) (.dec (.fin (decide (n < 0)) n.natAbs 0)) := by
      simp [richLt, richOrd, convert_rat c false a n d h, convert_dec]
    have hx := (comparisonsExact_proven c (scaleBy a d) (.fin (decide (n < 0)) n.natAbs 0) fl).1
    subst ha
    obtain ⟨q1, q2, _⟩ := hx rfl rfl
    exact ⟨by rw [h1, q1]; rfl, by rw [h2, q2]; rfl⟩
  · intro n d h
    unfold RatLimitsOk at h
    have key : ∀ eqOp, ∃ msg, (convertForComparison c eqOp a (.rat n d)).run fl = .error (.valueError msg) := by
      intro eqOp
      rcases a with ⟨s, co, e⟩ | s | ⟨s, t, p⟩
      · by_cases h1 : numDigits co > maxStrDigits
        · exact ⟨limitToIntMsg (numDigits co), by
            simp [convertForComparison, liftPy, intLimit, h1, StateT.run, bind, StateT.bind, Except.bind,
              Functor.map, Except.map]⟩
        by_cases h2 : numDigits (co * d) > maxStrDigits
        · exact ⟨limitToStrMsg, by
            simp [convertForComparison, liftPy, intLimit, strLimit, h1, h2, StateT.run, bind, StateT.bind,
              Except.bind, Functor.map, Except.map, pure, Except.pure, StateT.pure]⟩
        have h3 : numDigits n.natAbs > maxStrDigits := by simp at h; omega
        exact ⟨limitToStrMsg, by
          simp [convertForComparison, liftPy, intLimit, strLimit, pyFromInt, h1, h2, h3, StateT.run, bind,
            StateT.bind, Except.bind, Functor.map, Except.map, pure, Except.pure, StateT.pure]⟩
      · have h3 : numDigits n.natAbs > maxStrDigits := by simp at h; omega
        exact ⟨limitToStrMsg, by
          simp [convertForComparison, liftPy, strLimit, pyFromInt, h3, StateT.run, bind,
            StateT.bind, Except.bind, Functor.map, Except.map, pure, Except.pure, StateT.pure]⟩
      · have h3 : numDigits n.natAbs > maxStrDigits := by simp at h; omega
        exact ⟨limitToStrMsg, by
          simp [convertForComparison, liftPy, strLimit, pyFromInt, h3, StateT.run, bind,
            StateT.bind, Except.bind, Functor.map, Except.map, pure, Except.pure, StateT.pure]⟩
    have hb : ∀ {β : Type} (x : DM (Option (Dec × Dec))) (g : Option (Dec × Dec) → DM β) (msg : String),
        x.run fl = .error (.valueError msg) → (x >>= g).run fl = .error (.valueError msg) := by
      intro β x g msg hx
      simp only [StateT.run, bind, StateT.bind, Except.bind] at hx ⊢
      rw [hx]
    refine ⟨?_, fun t => ?_⟩
    · obtain ⟨msg, hm⟩ := key true
      exact ⟨msg, hb _ _ msg hm⟩
    · obtain ⟨msg, hm⟩ := key false
      exact ⟨msg, hb _ _ msg hm⟩
  · intro f x hx
    refine ⟨?_, fun t => ?_⟩
    · have : richEq c a (.float f) = (setFlag .floatOperation >>= fun _ => richEq c a (.dec x)) := by
        simp [richEq, convertForComparison, convertForComparison.floatCase, liftPy_pure hx]
      rw [this, run_setFlag_bind]
    · have : richOrd t c a (.float f) = (raiseSig c .floatOperation >>= fun _ => richOrd t c a (.dec x)) := by
        simp [richOrd, convertForComparison, convertForComparison.floatCase, liftPy_pure hx]
      rw [this, run_raiseSig_bind]; rfl
  · intro re im
    by_cases h : Binary64.F64.eq im (Binary64.F64.zero false) = true <;>
      simp [richEq, convertForComparison, h]
  · intro t re im; simp [richOrd, convertForComparison]
  · simp [richEq, convertForComparison]
  · intro t; simp [richOrd, convertForComparison]

end PyLean.Decimal
