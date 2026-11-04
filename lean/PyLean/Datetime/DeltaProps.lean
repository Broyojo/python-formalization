import PyLean.Datetime.Spec

/-!
`timedelta` with integer arguments: the C and Python constructors and number
methods agree, the constructor normalizes exactly, and `divmod` satisfies the
floor-division identity.
-/

namespace PyLean.Datetime

open PyLean

/-! ### Closed forms -/

/-- Microseconds of `timedelta.min` and one past `timedelta.max`. -/
def MIN_US : Int := -999999999 * 86400000000
def END_US : Int := 1000000000 * 86400000000

/-- The normalized `timedelta` of `T` microseconds, as Python builds it. -/
def mkDeltaPy (T : Int) : Py Delta :=
  if (T / 86400000000).natAbs > 999999999 then
    .error (.overflowError s!"timedelta # of days is too large: {T / 86400000000}")
  else .ok ⟨T / 86400000000, T / 1000000 % 86400, T % 1000000⟩

/-- The total of the constructor arguments in microseconds. -/
def totalUs (days seconds microseconds milliseconds minutes hours weeks : Int) : Int :=
  microseconds + milliseconds * 1000 + seconds * 1000000 + minutes * 60000000 +
    hours * 3600000000 + days * 86400000000 + weeks * 604800000000

theorem deltaPy_eq (days seconds microseconds milliseconds minutes hours weeks : Int) :
    deltaPy days seconds microseconds milliseconds minutes hours weeks =
      mkDeltaPy (totalUs days seconds microseconds milliseconds minutes hours weeks) := by
  simp only [deltaPy, mkDeltaPy, totalUs]
  have e1 : days + weeks * 7 + (seconds + minutes * 60 + hours * 3600) / 86400 +
      (microseconds + milliseconds * 1000) / 1000000 / 86400 +
      (0 + (seconds + minutes * 60 + hours * 3600) % 86400 +
        (microseconds + milliseconds * 1000) / 1000000 % 86400 +
        (microseconds + milliseconds * 1000) % 1000000 / 1000000) / 86400 = (microseconds + milliseconds * 1000 + seconds * 1000000 + minutes * 60000000 +
        hours * 3600000000 + days * 86400000000 + weeks * 604800000000) / 86400000000 := by
    omega
  have e2 : (0 + (seconds + minutes * 60 + hours * 3600) % 86400 +
        (microseconds + milliseconds * 1000) / 1000000 % 86400 +
        (microseconds + milliseconds * 1000) % 1000000 / 1000000) % 86400 = (microseconds + milliseconds * 1000 + seconds * 1000000 + minutes * 60000000 +
        hours * 3600000000 + days * 86400000000 + weeks * 604800000000) / 1000000 % 86400 := by
    omega
  have e3 : (microseconds + milliseconds * 1000) % 1000000 % 1000000 = (microseconds + milliseconds * 1000 + seconds * 1000000 + minutes * 60000000 +
        hours * 3600000000 + days * 86400000000 + weeks * 604800000000) % 1000000 := by omega
  rw [e1, e2, e3]
  exact rfl

theorem usToDeltaPy_eq (x : Int) : usToDeltaPy x = mkDeltaPy x := by
  rw [usToDeltaPy, deltaPy_eq]; simp [totalUs]

/-- The normalized `timedelta` of `T` microseconds, as C `new_delta` checks it. -/
def mkDeltaN (T : Int) : Py Delta :=
  if -MAX_DELTA_DAYS ≤ T / 86400000000 ∧ T / 86400000000 ≤ MAX_DELTA_DAYS then
    .ok ⟨T / 86400000000, T / 1000000 % 86400, T % 1000000⟩
  else .error (.overflowError s!"days={T / 86400000000}; must have magnitude <= 999999999")

theorem usToDeltaC_eq (x : Int) :
    usToDeltaC x = if fitsCInt (x / 86400000000) then mkDeltaN x
      else .error (.overflowError "Python int too large to convert to C int") := by
  have e : x / 1000000 / 86400 = x / 86400000000 := by omega
  simp only [usToDeltaC, asCInt, checkDeltaDayRange, mkDeltaN, fitsCInt, e]
  by_cases h1 : -2 ^ 31 ≤ x / 86400000000 ∧ x / 86400000000 ≤ 2 ^ 31 - 1
  · simp only [h1, and_self, ite_true]
    by_cases h2 : -MAX_DELTA_DAYS ≤ x / 86400000000 ∧ x / 86400000000 ≤ MAX_DELTA_DAYS
    · simp [h2, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]
    · simp [h2, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]
  · simp only [h1, ite_false]
    rfl

theorem normStep_us (s us : Int) :
    (if us < 0 ∨ us ≥ 1000000 then normalizePair s us 1000000 else (s, us)).1 * 1000000 +
      (if us < 0 ∨ us ≥ 1000000 then normalizePair s us 1000000 else (s, us)).2 = s * 1000000 + us ∧
    0 ≤ (if us < 0 ∨ us ≥ 1000000 then normalizePair s us 1000000 else (s, us)).2 ∧
    (if us < 0 ∨ us ≥ 1000000 then normalizePair s us 1000000 else (s, us)).2 < 1000000 := by
  by_cases h : us < 0 ∨ us ≥ 1000000
  · simp only [h, normalizePair, ite_true]; omega
  · simp only [h, ite_false, true_and]; omega

theorem normStep_s (d s : Int) :
    (if s < 0 ∨ s ≥ 86400 then normalizePair d s 86400 else (d, s)).1 * 86400 +
      (if s < 0 ∨ s ≥ 86400 then normalizePair d s 86400 else (d, s)).2 = d * 86400 + s ∧
    0 ≤ (if s < 0 ∨ s ≥ 86400 then normalizePair d s 86400 else (d, s)).2 ∧
    (if s < 0 ∨ s ≥ 86400 then normalizePair d s 86400 else (d, s)).2 < 86400 := by
  by_cases h : s < 0 ∨ s ≥ 86400
  · simp only [h, normalizePair, ite_true]; omega
  · simp only [h, ite_false, true_and]; omega

theorem newDeltaNormC_eq (d s us : Int) : newDeltaNormC d s us = mkDeltaN ((d * 86400 + s) * 1000000 + us) := by
  have h1 := normStep_us s us
  unfold newDeltaNormC
  generalize (if us < 0 ∨ us ≥ 1000000 then normalizePair s us 1000000 else (s, us)) = p1 at h1 ⊢
  obtain ⟨s1, us1⟩ := p1
  have h2 := normStep_s d s1
  simp only at h1 h2 ⊢
  generalize (if s1 < 0 ∨ s1 ≥ 86400 then normalizePair d s1 86400 else (d, s1)) = p2 at h2 ⊢
  obtain ⟨d2, s2⟩ := p2
  simp only at h2 ⊢
  have e1 : d2 = ((d * 86400 + s) * 1000000 + us) / 86400000000 := by omega
  have e2 : s2 = ((d * 86400 + s) * 1000000 + us) / 1000000 % 86400 := by omega
  have e3 : us1 = ((d * 86400 + s) * 1000000 + us) % 1000000 := by omega
  subst e1 e2 e3
  unfold checkDeltaDayRange mkDeltaN
  split <;> simp [*, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]

theorem sameOutcome_mkN (T : Int) : SameOutcome (mkDeltaPy T) (mkDeltaN T) := by
  unfold mkDeltaPy mkDeltaN MAX_DELTA_DAYS
  by_cases h : (T / 86400000000).natAbs > 999999999
  · have h2 : ¬(-999999999 ≤ T / 86400000000 ∧ T / 86400000000 ≤ 999999999) := by omega
    simp [h, h2, SameOutcome, PyExc.className]
  · have h2 : -999999999 ≤ T / 86400000000 ∧ T / 86400000000 ≤ 999999999 := by omega
    simp [h, h2, SameOutcome]

theorem sameOutcome_mk (T : Int) : SameOutcome (mkDeltaPy T) (usToDeltaC T) := by
  rw [usToDeltaC_eq]
  by_cases hf : fitsCInt (T / 86400000000)
  · rw [if_pos hf]; exact sameOutcome_mkN T
  · rw [if_neg hf]
    unfold fitsCInt at hf
    have h : (T / 86400000000).natAbs > 999999999 := by omega
    simp [mkDeltaPy, h, SameOutcome, PyExc.className]

theorem mkDeltaPy_spec (T : Int) :
    (∀ t, mkDeltaPy T = .ok t → t.Valid ∧ t.toUs = T) ∧
    ((∃ t, mkDeltaPy T = .ok t) ↔ MIN_US ≤ T ∧ T < END_US) ∧
    ((∃ t, mkDeltaPy T = .ok t) ∨ (mkDeltaPy T).raises "OverflowError") := by
  unfold mkDeltaPy MIN_US END_US
  by_cases h : (T / 86400000000).natAbs > 999999999
  · rw [if_pos h]
    refine ⟨fun t ht => ?_, ⟨fun ⟨t, ht⟩ => ?_, fun _ => ?_⟩, Or.inr ⟨_, rfl, rfl⟩⟩
    · cases ht
    · cases ht
    · omega
  · rw [if_neg h]
    refine ⟨fun t ht => ?_, ⟨fun _ => by omega, fun _ => ⟨_, rfl⟩⟩, Or.inl ⟨_, rfl⟩⟩
    cases ht
    unfold Delta.Valid Delta.toUs MAX_DELTA_DAYS
    simp only
    omega

/-! ### Properties -/

/-- `timedelta(days, seconds, microseconds, milliseconds, minutes, hours,
weeks)` with int arguments: C and Python agree on the result and on the
exception class, for all ints (C narrows the day count to `int` only after
dividing). -/
def TimedeltaCtorTwins : Prop :=
  ∀ days seconds microseconds milliseconds minutes hours weeks : Int,
    SameOutcome (deltaPy days seconds microseconds milliseconds minutes hours weeks)
      (deltaC days seconds microseconds milliseconds minutes hours weeks)

theorem timedeltaCtorTwins_proven : TimedeltaCtorTwins := by
  intro days seconds microseconds milliseconds minutes hours weeks
  rw [deltaPy_eq, deltaC]
  exact sameOutcome_mk _

/-- The constructor is exact: it returns a normalized timedelta
(`0 <= seconds < 86400`, `0 <= microseconds < 10**6`,
`|days| <= 999999999`) whose value is the sum of the arguments, exactly when
that sum lies in `[timedelta.min, timedelta.max]`, and raises `OverflowError`
otherwise. -/
def TimedeltaCtorExact : Prop :=
  ∀ days seconds microseconds milliseconds minutes hours weeks : Int,
    let T := totalUs days seconds microseconds milliseconds minutes hours weeks
    let r := deltaPy days seconds microseconds milliseconds minutes hours weeks
    (∀ t, r = .ok t → t.Valid ∧ t.toUs = T) ∧
    ((∃ t, r = .ok t) ↔ MIN_US ≤ T ∧ T < END_US) ∧
    ((∃ t, r = .ok t) ∨ r.raises "OverflowError")

theorem timedeltaCtorExact_proven : TimedeltaCtorExact := by
  intro days seconds microseconds milliseconds minutes hours weeks
  simp only [deltaPy_eq]
  exact mkDeltaPy_spec _

theorem toUs_valid_bounds (a : Delta) (ha : a.Valid) : MIN_US ≤ a.toUs ∧ a.toUs < END_US := by
  unfold Delta.Valid MAX_DELTA_DAYS at ha
  unfold Delta.toUs MIN_US END_US
  omega

theorem mkDeltaPy_of_valid (a : Delta) (ha : a.Valid) : mkDeltaPy a.toUs = .ok a := by
  unfold Delta.Valid MAX_DELTA_DAYS at ha
  unfold mkDeltaPy Delta.toUs
  have e1 : ((a.days * 86400 + a.seconds) * 1000000 + a.us) / 86400000000 = a.days := by omega
  have e2 : ((a.days * 86400 + a.seconds) * 1000000 + a.us) / 1000000 % 86400 = a.seconds := by omega
  have e3 : ((a.days * 86400 + a.seconds) * 1000000 + a.us) % 1000000 = a.us := by omega
  have h : ¬ (a.days.natAbs > 999999999) := by omega
  simp only [e1, e2, e3, h, ite_false]

theorem sameOutcome_bind {α β : Type} (x : Py α) (f g : α → Py β)
    (h : ∀ v, SameOutcome (f v) (g v)) : SameOutcome (x >>= f) (x >>= g) := by
  cases x with
  | error e => simp [bind, Except.bind, SameOutcome]
  | ok v => exact h v

theorem mul_total (a : Delta) (k : Int) :
    totalUs (a.days * k) (a.seconds * k) (a.us * k) 0 0 0 0 = k * a.toUs := by
  unfold totalUs Delta.toUs
  grind

theorem fmod_bounds (a b : Int) (hb : b ≠ 0) :
    (0 < b → 0 ≤ a.fmod b ∧ a.fmod b < b) ∧ (b < 0 → b < a.fmod b ∧ a.fmod b ≤ 0) := by
  refine ⟨fun h => ⟨Int.fmod_nonneg_of_pos a h, Int.fmod_lt_of_pos a h⟩, fun h => ?_⟩
  rw [Int.fmod_eq_emod]
  have h0 := Int.emod_nonneg a hb
  have h1 := Int.emod_lt a hb
  by_cases hd : b ∣ a
  · have : a % b = 0 := Int.emod_eq_zero_of_dvd hd
    simp [hd]; omega
  · have : a % b ≠ 0 := fun h' => hd (Int.dvd_of_emod_eq_zero h')
    have hn : ¬(0 ≤ b ∨ b ∣ a) := by omega
    simp only [hn, ite_false]
    omega

/-! ### `_divide_and_round` and C `divide_nearest` -/

/-- `q` is `a / b` rounded to the nearest integer, ties to even: `|a - q*b| <= |b|/2`, with
equality only for even `q`. -/
def RoundsHalfEven (a b q : Int) : Prop :=
  2 * (a - q * b).natAbs ≤ b.natAbs ∧ (2 * (a - q * b).natAbs = b.natAbs → q % 2 = 0)

theorem roundsHalfEven_unique (a b q1 q2 : Int) (hb : b ≠ 0) (h1 : RoundsHalfEven a b q1)
    (h2 : RoundsHalfEven a b q2) : q1 = q2 := by
  apply Classical.byContradiction
  intro hne
  have e : (a - q1 * b) - (a - q2 * b) = (q2 - q1) * b := by rw [Int.sub_mul]; omega
  have habs : ((q2 - q1) * b).natAbs = (q2 - q1).natAbs * b.natAbs := Int.natAbs_mul _ _
  have tri : ((a - q1 * b) - (a - q2 * b)).natAbs ≤ (a - q1 * b).natAbs + (a - q2 * b).natAbs := by
    omega
  rw [e, habs] at tri
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  have hq : (q2 - q1).natAbs = 1 := by
    apply Classical.byContradiction
    intro hq
    have : 2 * b.natAbs ≤ (q2 - q1).natAbs * b.natAbs := Nat.mul_le_mul_right _ (by omega)
    omega
  rw [hq, Nat.one_mul] at tri
  have := h1b (by omega)
  have := h2b (by omega)
  omega

theorem divideAndRound_spec (a b : Int) (hb : b ≠ 0) :
    ∃ q, divideAndRound a b = .ok q ∧ RoundsHalfEven a b q := by
  have hfb := fmod_bounds a b hb
  have hdm := Int.fdiv_mul_add_fmod a b
  unfold divideAndRound pyDivmod
  rw [if_neg hb]
  generalize a.fdiv b = q at hdm ⊢
  generalize a.fmod b = r at hdm hfb ⊢
  have e1 : (q + 1) * b = q * b + b := by rw [Int.add_mul, Int.one_mul]
  simp only [bind, Except.bind, pure, Except.pure]
  rcases Int.lt_or_gt_of_ne hb with h | h
  · have := hfb.2 h
    have hgt : ¬ b > 0 := by omega
    simp only [hgt, if_false]
    by_cases hc : r * 2 < b ∨ r * 2 = b ∧ q % 2 = 1
    · rw [if_pos hc]; refine ⟨_, rfl, ?_⟩; unfold RoundsHalfEven; rw [e1]; omega
    · rw [if_neg hc]; refine ⟨_, rfl, ?_⟩; unfold RoundsHalfEven; omega
  · have := hfb.1 h
    have hgt : b > 0 := h
    simp only [hgt, if_true]
    by_cases hc : r * 2 > b ∨ r * 2 = b ∧ q % 2 = 1
    · rw [if_pos hc]; refine ⟨_, rfl, ?_⟩; unfold RoundsHalfEven; rw [e1]; omega
    · rw [if_neg hc]; refine ⟨_, rfl, ?_⟩; unfold RoundsHalfEven; omega

theorem divideNearestC_spec (a b : Int) (hb : b ≠ 0) :
    ∃ q, divideNearestC a b = .ok q ∧ RoundsHalfEven a b q := by
  have hdm := Int.tmod_add_tdiv_mul a b
  have hab : (a.tmod b).natAbs = a.natAbs % b.natAbs := Int.natAbs_tmod a b
  have hlt : a.natAbs % b.natAbs < b.natAbs := Nat.mod_lt _ (by omega)
  have hsg : (0 ≤ a → 0 ≤ a.tmod b) ∧ (a < 0 → a.tmod b ≤ 0) := by
    refine ⟨fun h => Int.tmod_nonneg b h, fun h => ?_⟩
    have := Int.neg_tmod (-a) b
    rw [Int.neg_neg] at this
    have := Int.tmod_nonneg b (by omega : 0 ≤ -a)
    omega
  unfold divideNearestC
  rw [if_neg hb]
  generalize a.tdiv b = q at hdm ⊢
  generalize a.tmod b = r at hdm hab hsg ⊢
  have e1 : (q + 1) * b = q * b + b := by rw [Int.add_mul, Int.one_mul]
  have e2 : (q - 1) * b = q * b - b := by rw [Int.sub_mul, Int.one_mul]
  dsimp only
  rcases Int.lt_or_gt_of_ne hb with hb' | hb' <;> by_cases ha : a < 0
  · by_cases h1 : 2 * r < b <;> by_cases h2 : 2 * r = b <;> by_cases h3 : q.natAbs % 2 = 1 <;>
      simp [ha, hb', h1, h2, h3] <;> unfold RoundsHalfEven <;> (try simp only [e1, e2]) <;> omega
  · have hn : ¬ (b > 0) := by omega
    by_cases h1 : -(2 * r) < b <;> by_cases h2 : -(2 * r) = b <;> by_cases h3 : q.natAbs % 2 = 1 <;>
      simp [ha, hb', hn, h1, h2, h3] <;> unfold RoundsHalfEven <;> (try simp only [e1, e2]) <;> omega
  · have hn : ¬ (b < 0) := by omega
    by_cases h1 : -(2 * r) < b <;> by_cases h2 : -(2 * r) = b <;> by_cases h3 : q.natAbs % 2 = 1 <;>
      simp [ha, hn, h1, h2, h3] <;> unfold RoundsHalfEven <;> (try simp only [e1, e2]) <;> omega
  · have hn : ¬ (b < 0) := by omega
    by_cases h1 : 2 * r < b <;> by_cases h2 : 2 * r = b <;> by_cases h3 : q.natAbs % 2 = 1 <;>
      simp [ha, hn, h1, h2, h3] <;> unfold RoundsHalfEven <;> (try simp only [e1, e2]) <;> omega

/-- `_divide_and_round(a, b)` is C `divide_nearest(a, b)` (`_PyLong_DivmodNear`) for all ints;
for `b != 0` it is `a / b` rounded to the nearest integer with ties to even, and for `b == 0`
it raises `ZeroDivisionError`. Floor division in its place fails at `a = 3, b = 2`, rounding
half up at `a = 1, b = 2`. -/
def DivideAndRound : Prop :=
  ∀ a b : Int,
    divideAndRound a b = divideNearestC a b ∧
    (b = 0 → (divideAndRound a b).raises "ZeroDivisionError") ∧
    (b ≠ 0 → ∃ q, divideAndRound a b = .ok q ∧ RoundsHalfEven a b q)

theorem divideAndRound_proven : DivideAndRound := by
  intro a b
  by_cases hb : b = 0
  · subst hb
    refine ⟨rfl, fun _ => ⟨_, rfl, rfl⟩, fun h => absurd rfl h⟩
  · obtain ⟨q1, e1, r1⟩ := divideAndRound_spec a b hb
    obtain ⟨q2, e2, r2⟩ := divideNearestC_spec a b hb
    refine ⟨?_, fun h => absurd h hb, fun _ => ⟨q1, e1, r1⟩⟩
    rw [e1, e2, roundsHalfEven_unique a b q1 q2 hb r1 r2]

/-- The number methods of `timedelta` with timedelta and int operands: C and
Python agree on the result and the exception class, for all valid operands and
all ints `k`. -/
def TimedeltaOpsTwins : Prop :=
  ∀ (a b : Delta) (k : Int), a.Valid → b.Valid →
    SameOutcome (a.addPy b) (a.addC b) ∧ SameOutcome (a.subPy b) (a.subC b) ∧
    SameOutcome a.negPy a.negC ∧ SameOutcome a.absPy a.absC ∧
    SameOutcome (a.mulPy k) (a.mulC k) ∧ SameOutcome (a.floordivIntPy k) (a.floordivIntC k) ∧
    SameOutcome (a.truedivIntPy k) (a.truedivIntC k) ∧ SameOutcome (a.floordivPy b) (a.floordivC b) ∧
    SameOutcome (a.modPy b) (a.modC b) ∧ SameOutcome (a.divmodPy b) (a.divmodC b)

theorem negTwins (a : Delta) : SameOutcome a.negPy a.negC := by
  unfold Delta.negPy Delta.negC
  rw [deltaPy_eq, newDeltaNormC_eq]
  have : totalUs (-a.days) (-a.seconds) (-a.us) 0 0 0 0 = (-a.days * 86400 + -a.seconds) * 1000000 + -a.us := by
    unfold totalUs; omega
  rw [this]; exact sameOutcome_mkN _

theorem timedeltaOpsTwins_proven : TimedeltaOpsTwins := by
  intro a b k _ _
  refine ⟨?_, ?_, negTwins a, ?_, ?_, ?_, ?_, sameOutcome_refl _, ?_, ?_⟩
  · unfold Delta.addPy Delta.addC
    rw [deltaPy_eq, newDeltaNormC_eq]
    have : totalUs (a.days + b.days) (a.seconds + b.seconds) (a.us + b.us) 0 0 0 0 =
        ((a.days + b.days) * 86400 + (a.seconds + b.seconds)) * 1000000 + (a.us + b.us) := by
      unfold totalUs; omega
    rw [this]; exact sameOutcome_mkN _
  · unfold Delta.subPy Delta.subC
    rw [deltaPy_eq, newDeltaNormC_eq]
    have : totalUs (a.days - b.days) (a.seconds - b.seconds) (a.us - b.us) 0 0 0 0 =
        ((a.days - b.days) * 86400 + (a.seconds - b.seconds)) * 1000000 + (a.us - b.us) := by
      unfold totalUs; omega
    rw [this]; exact sameOutcome_mkN _
  · unfold Delta.absPy Delta.absC
    split
    · exact negTwins a
    · exact sameOutcome_refl _
  · unfold Delta.mulPy Delta.mulC
    rw [deltaPy_eq, mul_total]
    exact sameOutcome_mk _
  · unfold Delta.floordivIntPy Delta.floordivIntC
    apply sameOutcome_bind
    intro ⟨q, r⟩; simp only; rw [usToDeltaPy_eq]; exact sameOutcome_mk _
  · unfold Delta.truedivIntPy Delta.truedivIntC
    rw [← (divideAndRound_proven a.toUs k).1]
    apply sameOutcome_bind
    intro v; rw [usToDeltaPy_eq]; exact sameOutcome_mk _
  · unfold Delta.modPy Delta.modC
    apply sameOutcome_bind
    intro ⟨q, r⟩; simp only; rw [usToDeltaPy_eq]; exact sameOutcome_mk _
  · unfold Delta.divmodPy Delta.divmodC
    apply sameOutcome_bind
    intro ⟨q, r⟩
    simp only
    rw [usToDeltaPy_eq]
    have h := sameOutcome_mk r
    revert h
    cases mkDeltaPy r <;> cases usToDeltaC r <;> simp [SameOutcome, bind, Except.bind, pure, Except.pure]

/-- `divmod(a, b)` for timedeltas: for `b != 0` it returns
`(a // b, a % b)` with `q * b + r == a` and `r` zero or of the sign of `b`
with `|r| < |b|`; for `b == 0` it raises `ZeroDivisionError`. -/
def TimedeltaDivmod : Prop :=
  ∀ a b : Delta, a.Valid → b.Valid →
    (b.toUs ≠ 0 → ∃ q r, a.divmodPy b = .ok (q, r) ∧ a.floordivPy b = .ok q ∧ a.modPy b = .ok r ∧
      r.Valid ∧ q * b.toUs + r.toUs = a.toUs ∧
      (0 < b.toUs → 0 ≤ r.toUs ∧ r.toUs < b.toUs) ∧ (b.toUs < 0 → b.toUs < r.toUs ∧ r.toUs ≤ 0)) ∧
    (b.toUs = 0 → (a.divmodPy b).raises "ZeroDivisionError")

theorem timedeltaDivmod_proven : TimedeltaDivmod := by
  intro a b _ hb
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · have hfb := fmod_bounds a.toUs b.toUs h0
    have hbb := toUs_valid_bounds b hb
    have hin : MIN_US ≤ a.toUs.fmod b.toUs ∧ a.toUs.fmod b.toUs < END_US := by
      unfold MIN_US END_US at *
      by_cases hp : 0 < b.toUs
      · have := hfb.1 hp; omega
      · have := hfb.2 (by omega); omega
    obtain ⟨t, ht⟩ := (mkDeltaPy_spec (a.toUs.fmod b.toUs)).2.1.mpr hin
    have hts := (mkDeltaPy_spec (a.toUs.fmod b.toUs)).1 t ht
    refine ⟨a.toUs.fdiv b.toUs, t, ?_, ?_, ?_, hts.1, ?_, ?_, ?_⟩
    · simp [Delta.divmodPy, pyDivmod, h0, usToDeltaPy_eq, ht, bind, Except.bind, pure, Except.pure]
    · simp [Delta.floordivPy, pyDivmod, h0, bind, Except.bind, pure, Except.pure]
    · simp [Delta.modPy, pyDivmod, h0, usToDeltaPy_eq, ht, bind, Except.bind]
    · rw [hts.2]
      have := Int.fdiv_mul_add_fmod a.toUs b.toUs
      exact this
    · intro hp; rw [hts.2]; exact hfb.1 hp
    · intro hn; rw [hts.2]; exact hfb.2 hn
  · simp [Delta.divmodPy, pyDivmod, h0, bind, Except.bind, Py.raises, PyExc.className]

/-- `timezone(offset)`: both twins accept exactly the offsets strictly between
`-timedelta(hours=24)` and `timedelta(hours=24)`, return the same offset, and
otherwise raise `ValueError`. -/
def TimezoneRange : Prop :=
  ∀ t : Delta, t.Valid →
    ((∃ o, timezonePy t = .ok o) ↔ (-86400000000 < t.toUs ∧ t.toUs < 86400000000)) ∧
    (∀ o, timezonePy t = .ok o → o = t.toUs) ∧
    ((∃ o, timezonePy t = .ok o) ∨ (timezonePy t).raises "ValueError") ∧
    SameOutcome (timezonePy t) (newTimezoneC t)

theorem timezoneRange_proven : TimezoneRange := by
  intro t ht
  unfold Delta.Valid MAX_DELTA_DAYS at ht
  have hin : (-86400000000 < t.toUs ∧ t.toUs < 86400000000) ↔
      ¬((t.days = -1 ∧ t.seconds = 0 ∧ t.us < 1) ∨ t.days < -1 ∨ t.days ≥ 1) := by
    unfold Delta.toUs; omega
  unfold timezonePy newTimezoneC
  by_cases h0 : t.toUs = 0
  · simp only [h0, ite_true]
    refine ⟨⟨fun _ => by omega, fun _ => ⟨0, rfl⟩⟩, fun o ho => (by cases ho; rfl),
      Or.inl ⟨0, rfl⟩, rfl⟩
  · simp only [h0, ite_false]
    by_cases hr : -86399999999 ≤ t.toUs ∧ t.toUs ≤ 86399999999
    · have hc : ¬((t.days = -1 ∧ t.seconds = 0 ∧ t.us < 1) ∨ t.days < -1 ∨ t.days ≥ 1) :=
        hin.mp (by omega)
      rw [if_pos hr, if_neg hc]
      exact ⟨⟨fun _ => by omega, fun _ => ⟨_, rfl⟩⟩, fun o ho => (by cases ho; rfl), Or.inl ⟨_, rfl⟩, rfl⟩
    · have hc : ((t.days = -1 ∧ t.seconds = 0 ∧ t.us < 1) ∨ t.days < -1 ∨ t.days ≥ 1) := by
        have := mt hin.mpr; omega
      rw [if_neg hr, if_pos hc]
      refine ⟨⟨fun ⟨o, ho⟩ => (by cases ho), fun h => (by omega)⟩, fun o ho => (by cases ho),
        Or.inr ⟨_, rfl, rfl⟩, rfl⟩

end PyLean.Datetime
