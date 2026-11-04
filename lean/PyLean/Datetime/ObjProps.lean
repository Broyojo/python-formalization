import PyLean.Datetime.DeltaProps
import PyLean.Datetime.IsoCalProps
import PyLean.Datetime.Misc
import PyLean.Datetime.Strftime

/-!
Properties of `timedelta` and `date` beyond construction and arithmetic: comparison,
hash, pickle, weekday, time tuples, `ctime`, `repr`.
-/

namespace PyLean.Datetime

open PyLean

/-! ### Lexicographic helpers -/

theorem cmpTuple_nil : cmpTuple [] [] = 0 := rfl

/-- `_cmp` on tuples of equal length goes field by field. -/
theorem cmpTuple_cons (a b : Int) (x y : List Int) (h : x.length = y.length) :
    cmpTuple (a :: x) (b :: y) = if a = b then cmpTuple x y else if a < b then -1 else 1 := by
  unfold cmpTuple
  by_cases hab : a = b
  · subst hab
    simp [tupleLt]
  · have hne : ¬ (a :: x = b :: y) := by simp [hab]
    have hba : b ≠ a := fun e => hab e.symm
    rw [if_neg hne, if_neg hab]
    simp only [tupleLt, hba, ite_false]
    by_cases hlt : a < b
    · have : ¬ b < a := by omega
      simp [this, hlt]
    · have : b < a := by omega
      simp [this, hlt]

theorem cmpTuple_sign (x y : List Int) (h : x.length = y.length) :
    cmpTuple x y = 0 ↔ x = y := by
  unfold cmpTuple
  by_cases he : x = y
  · simp [he]
  · simp only [he, ite_false]
    split <;> simp

/-- `memcmp` of a byte against a byte. -/
theorem mc_field (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (x y : List Nat) :
    memcmpBytes (a.toNat :: x) (b.toNat :: y) =
      if a = b then memcmpBytes x y else if a < b then -1 else 1 := by
  simp only [memcmpBytes]
  by_cases h : a = b
  · subst h; simp
  · have : ¬ a.toNat = b.toNat := by omega
    simp only [this, h, ite_false]
    by_cases hl : a < b
    · have : a.toNat < b.toNat := by omega
      simp [this, hl]
    · have : ¬ a.toNat < b.toNat := by omega
      simp [this, hl]

/-- `memcmp` of a big-endian two-byte year. -/
theorem mc_year (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (x y : List Nat) :
    memcmpBytes ((a / 256).toNat :: (a % 256).toNat :: x) ((b / 256).toNat :: (b % 256).toNat :: y) =
      if a = b then memcmpBytes x y else if a < b then -1 else 1 := by
  rw [mc_field _ _ (by omega) (by omega), mc_field _ _ (by omega) (by omega)]
  by_cases h : a = b
  · subst h; simp
  · by_cases h1 : a / 256 = b / 256
    · have h2 : ¬ a % 256 = b % 256 := by omega
      simp only [h1, h2, h, ite_true, ite_false]
      by_cases hl : a < b
      · have : a % 256 < b % 256 := by omega
        simp [this, hl]
      · have : ¬ a % 256 < b % 256 := by omega
        simp [this, hl]
    · simp only [h1, h, ite_false]
      by_cases hl : a < b
      · have : a / 256 < b / 256 := by omega
        simp [this, hl]
      · have : ¬ a / 256 < b / 256 := by omega
        simp [this, hl]

/-- `memcmp` of a big-endian three-byte microsecond field at the end of the data. -/
theorem mc_us (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : a < 1000000) (hb' : b < 1000000) :
    memcmpBytes [(a / 65536).toNat, (a / 256 % 256).toNat, (a % 256).toNat]
      [(b / 65536).toNat, (b / 256 % 256).toNat, (b % 256).toNat] =
      if a = b then 0 else if a < b then -1 else 1 := by
  rw [mc_field _ _ (by omega) (by omega), mc_field _ _ (by omega) (by omega),
    mc_field _ _ (by omega) (by omega)]
  simp only [memcmpBytes]
  by_cases h : a = b
  · subst h; simp
  · simp only [h, ite_false]
    by_cases hl : a < b
    · simp only [hl, ite_true]
      split
      · split
        · split
          · omega
          · rename_i h3; omega
        · split
          · rfl
          · omega
      · split
        · rfl
        · omega
    · simp only [hl, ite_false]
      split
      · split
        · split
          · omega
          · split
            · omega
            · rfl
        · split
          · omega
          · rfl
      · split
        · omega
        · rfl

/-! ### `timedelta` -/

/-- The comparison `x op y` of two integers, the order the operators are meant to compute. -/
def CmpOp.holds : CmpOp → Int → Int → Bool
  | .lt, x, y => decide (x < y)
  | .le, x, y => decide (x ≤ y)
  | .eq, x, y => decide (x = y)
  | .ne, x, y => !decide (x = y)
  | .gt, x, y => decide (x > y)
  | .ge, x, y => decide (x ≥ y)

/-- A three-way result `c` with the sign of `x - y` gives every operator its meaning, through
C's `diff_to_bool`. -/
theorem diffToBool_holds (op : CmpOp) (c x y : Int) (h0 : c = 0 ↔ x = y) (hlt : c < 0 ↔ x < y) :
    diffToBool c op = op.holds x y := by
  have : (c < 0 ∧ x < y) ∨ (c = 0 ∧ x = y) ∨ (0 < c ∧ y < x) := by
    rcases Int.lt_trichotomy x y with h | h | h
    · exact Or.inl ⟨hlt.mpr h, h⟩
    · exact Or.inr (Or.inl ⟨h0.mpr h, h⟩)
    · have h1 : ¬ c < 0 := fun hc => by have := hlt.mp hc; omega
      have h2 : ¬ c = 0 := fun hc => by have := h0.mp hc; omega
      exact Or.inr (Or.inr ⟨by omega, h⟩)
  rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases op <;>
    simp only [diffToBool, CmpOp.holds, ← decide_not] <;> rw [decide_eq_decide] <;>
    constructor <;> intro <;> omega

/-- `timedelta` comparison: every operator of each twin computes the order of the durations
(`toUs`), for all valid operands. Precondition: the type invariant. A `__le__` computing
`< 0`, or a shared helper with a wrong case, fails at `a == b`. -/
def TimedeltaCompare : Prop :=
  ∀ (a b : Delta) (op : CmpOp), a.Valid → b.Valid →
    a.richPy op b = op.holds a.toUs b.toUs ∧ a.richC op b = op.holds a.toUs b.toUs

theorem delta_cmp_eq (a b : Delta) (ha : a.Valid) (hb : b.Valid) :
    a.cmpPy b = (if a.toUs = b.toUs then 0 else if a.toUs < b.toUs then -1 else 1) ∧
    (a.cmpC b = 0 ↔ a.toUs = b.toUs) ∧ (a.cmpC b < 0 ↔ a.toUs < b.toUs) := by
  unfold Delta.Valid MAX_DELTA_DAYS at ha hb
  obtain ⟨d1, s1, u1⟩ := a
  obtain ⟨d2, s2, u2⟩ := b
  simp only at ha hb
  unfold Delta.cmpPy Delta.cmpC Delta.getstate Delta.toUs
  simp only
  rw [cmpTuple_cons d1 d2 [s1, u1] [s2, u2] rfl, cmpTuple_cons s1 s2 [u1] [u2] rfl, cmpTuple_cons u1 u2 [] [] rfl,
    cmpTuple_nil]
  refine ⟨?_, ?_, ?_⟩
  · repeat' split
    all_goals first | rfl | omega
  · split <;> (try split) <;> omega
  · split <;> (try split) <;> omega

/-- The Python operators, each from its own line of the source, against the order. -/
theorem richPy_holds (op : CmpOp) (c x y : Int) (h0 : c = 0 ↔ x = y) (hlt : c < 0 ↔ x < y) :
    (match op with
      | .eq => decide (c = 0) | .ne => !decide (c = 0) | .le => decide (c ≤ 0)
      | .lt => decide (c < 0) | .ge => decide (c ≥ 0) | .gt => decide (c > 0)) = op.holds x y := by
  rw [← diffToBool_holds op c x y h0 hlt]
  cases op <;> rfl

theorem timedeltaCompare_proven : TimedeltaCompare := by
  intro a b op ha hb
  obtain ⟨h1, h2, h3⟩ := delta_cmp_eq a b ha hb
  have p0 : a.cmpPy b = 0 ↔ a.toUs = b.toUs := by rw [h1]; split <;> (try split) <;> omega
  have p1 : a.cmpPy b < 0 ↔ a.toUs < b.toUs := by rw [h1]; split <;> (try split) <;> omega
  refine ⟨?_, ?_⟩
  · unfold Delta.richPy
    exact richPy_holds op _ _ _ p0 p1
  · unfold Delta.richC
    exact diffToBool_holds op _ _ _ h2 h3

/-- `bool(t)` is `t != timedelta(0)`; the hash key of each twin is the state tuple
`(days, seconds, microseconds)`, so the twins hash alike, and two valid timedeltas have the
same key exactly when they are equal (a constant key fails). -/
def TimedeltaBoolHash : Prop :=
  ∀ a b : Delta, a.Valid → b.Valid →
    (a.bool = true ↔ a.toUs ≠ 0) ∧ (a.hashKey = b.hashKey ↔ a.toUs = b.toUs) ∧
    a.hashKey = a.hashKeyC

theorem timedeltaBoolHash_proven : TimedeltaBoolHash := by
  intro a b ha hb
  refine ⟨?_, ?_, rfl⟩
  · have ha' := ha
    unfold Delta.Valid MAX_DELTA_DAYS at ha'
    unfold Delta.bool Delta.toUs
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq]
    omega
  · unfold Delta.Valid MAX_DELTA_DAYS at ha hb
    unfold Delta.hashKey Delta.getstate Delta.toUs
    simp only [HashKey.ints.injEq, List.cons.injEq, and_true]
    omega

/-- `timedelta(*t.__reduce__()[1]) == t`, through `.days`, `.seconds`,
`.microseconds`, in both twins. -/
def TimedeltaReduce : Prop :=
  ∀ a : Delta, a.Valid →
    deltaPy (a.reduceArgs.getD 0 0) (a.reduceArgs.getD 1 0) (a.reduceArgs.getD 2 0) 0 0 0 0 = .ok a ∧
    deltaC (a.reduceArgs.getD 0 0) (a.reduceArgs.getD 1 0) (a.reduceArgs.getD 2 0) 0 0 0 0 = .ok a

theorem usToDeltaC_of_valid (a : Delta) (ha : a.Valid) : usToDeltaC a.toUs = .ok a := by
  have h := sameOutcome_mk a.toUs
  rw [mkDeltaPy_of_valid a ha] at h
  revert h
  cases hc : usToDeltaC a.toUs with
  | error e => simp [SameOutcome]
  | ok v => simp only [SameOutcome]; intro h; rw [h]

theorem timedeltaReduce_proven : TimedeltaReduce := by
  intro a ha
  have eT : totalUs a.days a.seconds a.us 0 0 0 0 = a.toUs := by
    unfold totalUs Delta.toUs; omega
  have e0 : a.reduceArgs.getD 0 0 = a.days := rfl
  have e1 : a.reduceArgs.getD 1 0 = a.seconds := rfl
  have e2 : a.reduceArgs.getD 2 0 = a.us := rfl
  rw [e0, e1, e2]
  constructor
  · rw [deltaPy_eq, eT]; exact mkDeltaPy_of_valid a ha
  · have : a.us + 0 * 1000 + a.seconds * 1000000 + 0 * 60000000 + 0 * 3600000000 + a.days * 86400000000 +
        0 * 604800000000 = a.toUs := by unfold Delta.toUs; omega
    rw [deltaC, this]; exact usToDeltaC_of_valid a ha

/-- `+t` for a valid `t` of the base type: Python returns the receiver itself (`+t is t`);
C `delta_positive` passes its day-range check and returns a new, equal timedelta, except for
the zero timedelta, which is the `zero_delta` singleton and so is the receiver. -/
def TimedeltaPos : Prop :=
  ∀ a : Delta, a.Valid → a.posPy = .self_ ∧
    a.posC = .ok (if a.toUs = 0 then .self_ else .fresh a)

theorem timedeltaPos_proven : TimedeltaPos := by
  intro a ha
  refine ⟨rfl, ?_⟩
  unfold Delta.Valid at ha
  unfold Delta.posC checkDeltaDayRange
  have : -MAX_DELTA_DAYS ≤ a.days ∧ a.days ≤ MAX_DELTA_DAYS := ⟨ha.2.2.2.2.1, ha.2.2.2.2.2⟩
  have hz : (a.days = 0 ∧ a.seconds = 0 ∧ a.us = 0) ↔ a.toUs = 0 := by
    unfold Delta.toUs; unfold MAX_DELTA_DAYS at this; omega
  simp only [this, and_self, ite_true, bind, Except.bind]
  by_cases h0 : a.toUs = 0
  · rw [if_pos (hz.mpr h0), if_pos h0]; rfl
  · rw [if_neg (fun h => h0 (hz.mp h)), if_neg h0]; rfl

/-- The reflected `a.__rsub__(b)` is `b - a` in both twins, for all valid operands. -/
def TimedeltaRsubTwins : Prop :=
  ∀ a b : Delta, a.Valid → b.Valid → SameOutcome (a.rsubPy b) (a.rsubC b)

/-- `timedelta.max.__rsub__(timedelta.max)`: Python computes `-self + other` and `-self`
overflows; C computes `other - self`, which is `timedelta(0)`. -/
theorem timedeltaRsubTwins_refuted : ¬TimedeltaRsubTwins := by
  intro h
  have := h ⟨999999999, 86399, 999999⟩ ⟨999999999, 86399, 999999⟩ (by decide) (by decide)
  have e1 : Delta.rsubC ⟨999999999, 86399, 999999⟩ ⟨999999999, 86399, 999999⟩ = .ok ⟨0, 0, 0⟩ := by
    decide
  have e2 : Delta.rsubPy ⟨999999999, 86399, 999999⟩ ⟨999999999, 86399, 999999⟩ =
      .error (.overflowError "timedelta # of days is too large: -1000000000") := by decide
  rw [e1, e2] at this
  exact this

/-- The reflected `a.__rsub__(b)` is `b - a` in both twins whenever `-a` is a timedelta; when
it is not (`a.days == 999999999` and `a` beyond `timedelta(999999999)`), Python raises
`OverflowError`. -/
def TimedeltaRsub : Prop :=
  ∀ a b : Delta, a.Valid → b.Valid →
    (MIN_US ≤ -a.toUs → SameOutcome (a.rsubPy b) (a.rsubC b)) ∧
    (-a.toUs < MIN_US → (a.rsubPy b).raises "OverflowError")

theorem timedeltaRsub_proven : TimedeltaRsub := by
  intro a b ha hb
  have hn : deltaPy (-a.days) (-a.seconds) (-a.us) 0 0 0 0 = mkDeltaPy (-a.toUs) := by
    rw [deltaPy_eq]; congr 1; unfold totalUs Delta.toUs; omega
  refine ⟨fun hneg => ?_, fun hneg => ?_⟩
  · unfold Delta.rsubPy Delta.rsubC Delta.negPy Delta.addPy Delta.subC
    rw [newDeltaNormC_eq]
    have ba := (toUs_valid_bounds a ha)
    rw [hn]
    obtain ⟨hv, hin, -⟩ := mkDeltaPy_spec (-a.toUs)
    by_cases hr : MIN_US ≤ -a.toUs ∧ -a.toUs < END_US
    · obtain ⟨n, hnn⟩ := hin.mpr hr
      have hnv := hv n hnn
      rw [hnn]
      show SameOutcome (deltaPy (n.days + b.days) (n.seconds + b.seconds) (n.us + b.us) 0 0 0 0) _
      rw [deltaPy_eq]
      have e1 : totalUs (n.days + b.days) (n.seconds + b.seconds) (n.us + b.us) 0 0 0 0 = n.toUs + b.toUs := by
        unfold totalUs Delta.toUs; omega
      have e2 : (b.days - a.days) * 86400 + (b.seconds - a.seconds) = (b.days * 86400 + b.seconds) - (a.days * 86400 + a.seconds) := by
        omega
      rw [e1, e2]
      have e3 : ((b.days * 86400 + b.seconds) - (a.days * 86400 + a.seconds)) * 1000000 + (b.us - a.us) = n.toUs + b.toUs := by
        rw [hnv.2]; unfold Delta.toUs; omega
      rw [e3]
      exact sameOutcome_mkN _
    · exfalso; apply hr; unfold MIN_US END_US at *; omega
  · unfold Delta.rsubPy Delta.negPy
    rw [hn]
    obtain ⟨-, hin, hor⟩ := mkDeltaPy_spec (-a.toUs)
    rcases hor with ⟨t, ht⟩ | ⟨e, he, hc⟩
    · exfalso; have := hin.mp ⟨t, ht⟩; omega
    · rw [he]; exact ⟨e, rfl, hc⟩

end PyLean.Datetime
