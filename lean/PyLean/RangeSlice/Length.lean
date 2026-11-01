import PyLean.RangeSlice.Spec

/-!
Range length: the unsigned-long fast path `get_len_of_range` agrees with the
PyLong slow path of `compute_range_length`, both compute the mathematical
length for every Python int, and `len()` raises `OverflowError` exactly when
that length exceeds `sys.maxsize`.
-/

namespace PyLean.RangeSlice

open PyLean

/-! ### Arithmetic lemmas -/

theorem ite_t {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem ite_f {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : ¬c) : (if c then a else b) = b := by
  simp [h]

theorem isLen_unique {a b s L₁ L₂ : Int} (h₁ : IsLen a b s L₁) (h₂ : IsLen a b s L₂) :
    L₁ = L₂ := by
  obtain ⟨h₁0, h₁⟩ := h₁
  obtain ⟨h₂0, h₂⟩ := h₂
  rcases Int.lt_trichotomy L₁ L₂ with h | h | h
  · have := (h₂ L₁ h₁0).1 h
    have := (h₁ L₁ h₁0).2 this
    omega
  · exact h
  · have := (h₁ L₂ h₂0).1 h
    have := (h₂ L₂ h₂0).2 this
    omega

/-- The slow path computes the mathematical length. -/
theorem slow_isLen (a b s : Int) (hs : s ≠ 0) : IsLen a b s (computeRangeLengthSlow a b s) := by
  unfold computeRangeLengthSlow IsLen InSeq
  by_cases hp : s > 0
  · rw [ite_t hp]
    by_cases hab : a ≥ b
    · rw [ite_t hab]
      refine ⟨Int.le_refl 0, fun k hk => ?_⟩
      have := Int.mul_nonneg hk (Int.le_of_lt hp)
      rw [ite_t (show (0 : Int) < s from hp)]
      omega
    · rw [ite_f hab]
      have hq := Int.ediv_nonneg (show 0 ≤ b - a - 1 by omega) (Int.le_of_lt hp)
      refine ⟨by omega, fun k hk => ?_⟩
      have := Int.le_ediv_iff_mul_le (a := k) (b := b - a - 1) hp
      rw [ite_t (show (0 : Int) < s from hp)]
      omega
  · have hn : s < 0 := by omega
    rw [ite_f hp]
    by_cases hab : b ≥ a
    · rw [ite_t hab]
      refine ⟨Int.le_refl 0, fun k hk => ?_⟩
      have := Int.mul_nonpos_of_nonneg_of_nonpos hk (Int.le_of_lt hn)
      rw [ite_f (show ¬ (0 : Int) < s by omega)]
      omega
    · rw [ite_f hab]
      have hq := Int.ediv_nonneg (show 0 ≤ a - b - 1 by omega) (show 0 ≤ -s by omega)
      refine ⟨by omega, fun k hk => ?_⟩
      have := Int.le_ediv_iff_mul_le (a := k) (b := a - b - 1) (show 0 < -s by omega)
      rw [Int.mul_neg] at this
      rw [ite_f (show ¬ (0 : Int) < s by omega)]
      omega

/-- `get_len_of_range` in unsigned long arithmetic equals the PyLong formula
for all C `long` arguments with a non-zero step. -/
theorem getLenOfRange_eq (lo hi step : Int) (hlo : IsLong lo) (hhi : IsLong hi)
    (hs : IsLong step) (h0 : step ≠ 0) :
    getLenOfRange lo hi step = computeRangeLengthSlow lo hi step := by
  unfold IsLong longMin longMax at hlo hhi hs
  unfold getLenOfRange computeRangeLengthSlow
  by_cases h1 : step > 0 ∧ lo < hi
  · rw [ite_t h1, ite_t h1.1, ite_f (show ¬ lo ≥ hi by omega)]
    have hX : usub (usub (toU hi) 1) (toU lo) = hi - lo - 1 := by
      unfold usub toU two64; omega
    have hS : toU step = step := by unfold toU two64; omega
    rw [hX, hS]
    have hq := Int.ediv_le_self step (show 0 ≤ hi - lo - 1 by omega)
    have hq0 := Int.ediv_nonneg (show 0 ≤ hi - lo - 1 by omega) (show 0 ≤ step by omega)
    unfold uadd two64
    omega
  · rw [ite_f h1]
    by_cases h2 : step < 0 ∧ lo > hi
    · rw [ite_t h2, ite_f (show ¬ step > 0 by omega), ite_f (show ¬ hi ≥ lo by omega)]
      have hX : usub (usub (toU lo) 1) (toU hi) = lo - hi - 1 := by
        unfold usub toU two64; omega
      have hS : usub 0 (toU step) = -step := by unfold usub toU two64; omega
      rw [hX, hS]
      have hq := Int.ediv_le_self (-step) (show 0 ≤ lo - hi - 1 by omega)
      have hq0 := Int.ediv_nonneg (show 0 ≤ lo - hi - 1 by omega) (show 0 ≤ -step by omega)
      unfold uadd two64
      omega
    · rw [ite_f h2]
      by_cases hp : step > 0
      · rw [ite_t hp, ite_t (show lo ≥ hi by omega)]
      · rw [ite_f hp, ite_t (show hi ≥ lo by omega)]

/-! ### Properties -/

/-- Fast path vs slow path: whenever `compute_range_length_long` (the C
`long` fast path, rangeobject.c:202-236) produces a length, it equals what the
PyLong slow path (rangeobject.c:264-313) computes for the same arguments.
Hypothesis `step ≠ 0` is a documented precondition (`get_len_of_range`
asserts it; `validate_step` guarantees it). -/
def RangeLengthFastSlow : Prop :=
  ∀ start stop step len : Int, step ≠ 0 →
    computeRangeLengthLong start stop step = some len →
    len = computeRangeLengthSlow start stop step

theorem rangeLengthFastSlow_proven : RangeLengthFastSlow := by
  intro start stop step len h0 h
  unfold computeRangeLengthLong asLong at h
  by_cases ha : IsLong start <;> by_cases hb : IsLong stop <;> by_cases hc : IsLong step <;>
    simp [ha, hb, hc] at h
  obtain ⟨-, rfl⟩ := h
  exact getLenOfRange_eq start stop step ha hb hc h0

theorem computeRangeLength_eq_slow (start stop step : Int) (h0 : step ≠ 0) :
    computeRangeLength start stop step = computeRangeLengthSlow start stop step := by
  unfold computeRangeLength
  split
  · rename_i len h
    exact rangeLengthFastSlow_proven start stop step len h0 h
  · rfl

theorem computeRangeLength_isLen (start stop step : Int) (h0 : step ≠ 0) :
    IsLen start stop step (computeRangeLength start stop step) := by
  rw [computeRangeLength_eq_slow _ _ _ h0]; exact slow_isLen _ _ _ h0

theorem Range.WF.len {r : Range} (h : r.WF) : r.Len r.length := by
  unfold Range.Len; rw [h.2]; exact computeRangeLength_isLen _ _ _ h.1

theorem Range.WF.length_eq {r : Range} (h : r.WF) {L : Int} (hL : r.Len L) : r.length = L :=
  isLen_unique h.len hL

theorem makeRangeObject_wf (a b s : Int) (h : s ≠ 0) : (makeRangeObject a b s).WF :=
  ⟨h, rfl⟩

theorem rangeNew_wf {a b : Int} {s : Option Int} {r : Range} (h : rangeNew a b s = .ok r) :
    r.WF := by
  unfold rangeNew validateStep at h
  cases s with
  | none => simp [bind, Except.bind, pure, Except.pure] at h; subst h; exact makeRangeObject_wf _ _ _ (by decide)
  | some v =>
    by_cases hv : v = 0
    · simp [hv, bind, Except.bind] at h
    · simp [hv, bind, Except.bind, pure, Except.pure] at h; subst h; exact makeRangeObject_wf _ _ _ hv

theorem range1_wf (b : Int) : (range1 b).WF := makeRangeObject_wf _ _ _ (by decide)

/-- `range(start, stop, step)` raises `ValueError` for a zero step and
otherwise stores the mathematical length, for every Python int; no argument
is too large. -/
def RangeNewLength : Prop :=
  ∀ (start stop : Int) (step : Option Int),
    (step = some 0 → rangeNew start stop step = .error (.valueError "range() arg 3 must not be zero")) ∧
    (step ≠ some 0 → ∃ r, rangeNew start stop step = .ok r ∧ r.start = start ∧ r.stop = stop ∧
      r.step = step.getD 1 ∧ r.Len r.length)

theorem rangeNewLength_proven : RangeNewLength := by
  intro start stop step
  refine ⟨fun h => by subst h; rfl, fun h => ?_⟩
  have hs : step.getD 1 ≠ 0 := by
    cases step with
    | none => decide
    | some v => simp only [Option.getD_some]; intro hv; exact h (by rw [hv])
  refine ⟨makeRangeObject start stop (step.getD 1), ?_, rfl, rfl, rfl,
    (makeRangeObject_wf _ _ _ hs).len⟩
  unfold rangeNew validateStep
  cases step with
  | none => rfl
  | some v =>
    have : v ≠ 0 := fun hv => h (by rw [hv])
    simp [this, bind, Except.bind, pure, Except.pure]

/-- `len(r)` returns the mathematical length `L` when `L <= sys.maxsize` and
raises `OverflowError` otherwise ("Ranges containing absolute values larger
than sys.maxsize are permitted but some features (such as len()) may raise
OverflowError", Doc/library/stdtypes.rst). `r.WF` is the type invariant. -/
def LenOverflow : Prop :=
  ∀ (r : Range) (L : Int), r.WF → r.Len L →
    rangeLength r = if L ≤ ssizeMax then .ok L else .error ssizeOverflow

theorem lenOverflow_proven : LenOverflow := by
  intro r L hw hL
  rw [← hw.length_eq hL]
  rfl

end PyLean.RangeSlice
