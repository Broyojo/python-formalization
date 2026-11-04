import PyLean.Datetime.TdFloat
import PyLean.Binary64.Props2
import PyLean.Datetime.DeltaProps

/-!
`timedelta.__new__` (Lib/_pydatetime.py:657-768) on exact binary64 floats: the int path of
`deltaNumPy` is the int model `deltaPy` (so `TimedeltaCtorTwins` and `TimedeltaCtorExact` hold
for it), and the twins agree for every combination of ints and integral-valued floats of
moderate size, the case the refuted `TimedeltaFloatCtorTwins` leaves standing. CPython 3.15.2.
-/

namespace PyLean.Datetime

open PyLean PyLean.Binary64 PyLean.Binary64.F64

/-! ### Integral doubles -/

theorem floor_half_add (k : Int) : ((k : Rat) + mkRat 1 2).floor = k := by
  rw [Rat.add_comm, Rat.floor_add_intCast]
  have : (mkRat 1 2).floor = 0 := by decide
  rw [this, Int.zero_add]

/-- C `round` of an integral double is itself. -/
theorem roundAway_int {y : F64} {t : Int} (hy : y.isFinite = true) (ht : y.toRat = t) (hb : t.natAbs < 2 ^ 53) :
    (F64.roundAway y).isFinite = true ∧ (F64.roundAway y).toRat = t := by
  have hn := isNaN_false_of_finite hy
  by_cases hz : y.isZero = true
  · have e : F64.roundAway y = y := by simp [F64.roundAway, hn, hy, hz]
    rw [e]; exact ⟨hy, ht⟩
  · have hz' : y.isZero = false := by simpa using hz
    have ht0 : t ≠ 0 := by
      intro h0
      have : y.isZero = true := (isZero_iff_toRat hy).2 (by rw [ht, h0]; rfl)
      rw [this] at hz'; cases hz'
    have e : F64.roundAway y = F64.ofIntS y.sign t := by
      simp only [F64.roundAway, hn, hy, hz', Bool.not_true, Bool.false_or, Bool.false_eq_true, ite_false]
      rw [ht]
      cases y.sign
      · simp only [Bool.false_eq_true, ite_false]
        rw [floor_half_add t]
      · simp only [ite_true]
        rw [← Rat.intCast_neg, floor_half_add (-t), Int.neg_neg]
    rw [e]
    unfold F64.ofIntS
    rw [if_neg ht0]
    exact ofInt_small hb

theorem dHalf_facts : dHalf.isFinite = true ∧ dHalf.toRat ≠ 0 := by decide +kernel

/-- Python's `round()` of an integral double (`float_round_int`: C `round`, then the
half-way correction, which does not fire) is the integer. -/
theorem round_int_value {y : F64} {t : Int} (hy : y.isFinite = true) (ht : y.toRat = t) (hb : t.natAbs < 2 ^ 53) :
    float_round_int y = .ok t := by
  obtain ⟨hrf, hrv⟩ := roundAway_int hy ht hb
  have hnf : (F64.roundAway y).neg.isFinite = true := by rw [neg_isFinite]; exact hrf
  have hsub : (F64.sub y (F64.roundAway y)).isFinite = true ∧ (F64.sub y (F64.roundAway y)).toRat = 0 := by
    unfold F64.sub
    rw [add_of_finite hy hnf, toRat_neg, ht, hrv]
    simp only [Rat.add_neg_cancel, ite_true]
    exact ⟨zero_isFinite _, zero_toRat _⟩
  have habs : (F64.sub y (F64.roundAway y)).abs.isFinite = true ∧ (F64.sub y (F64.roundAway y)).abs.toRat = 0 := by
    unfold F64.abs
    split
    · rw [neg_isFinite, toRat_neg, hsub.2]; exact ⟨hsub.1, by decide⟩
    · exact hsub
  have heq : F64.eq (F64.sub y (F64.roundAway y)).abs dHalf = false := by
    rw [eq_of_finite habs.1 dHalf_facts.1, habs.2]
    exact decide_eq_false (fun h => dHalf_facts.2 h.symm)
  unfold float_round_int
  simp only [heq, Bool.false_eq_true, ite_false]
  simp [PyLong_FromDouble, isInf_false_of_finite hrf, isNaN_false_of_finite hrf, truncInt_of_int hrv]

theorem tdToFloat_small {m : Int} (hb : m.natAbs < 2 ^ 53) : tdToFloat m = .ok (F64.ofInt m) := by
  have h := ofInt_small hb
  simp [tdToFloat, PyLong_AsDouble, isInf_false_of_finite h.1]

theorem mul_zero_f1e6 : F64.mul (F64.zero false) f1e6 = F64.zero false := by decide +kernel

theorem add_ofInt_zero {m : Int} (hb : m.natAbs < 2 ^ 53) :
    (F64.add (F64.ofInt m) (F64.zero false)).isFinite = true ∧ (F64.add (F64.ofInt m) (F64.zero false)).toRat = m := by
  have h := ofInt_small hb
  rw [add_of_finite h.1 (zero_isFinite false), h.2, zero_toRat]
  split
  · rename_i h0
    rw [Rat.add_zero] at h0
    exact ⟨zero_isFinite _, by rw [zero_toRat, h0]⟩
  · rw [Rat.add_zero]
    exact ofInt_small hb

/-- `round(microseconds + usdouble)` on the int branch (Py:744): `microseconds` is
`m % 10**6` and `usdouble` is `0.0 * 1e6`. -/
theorem round_mod (n : Int) :
    (do float_round_int (F64.add (← tdToFloat (n % 1000000)) (F64.mul (F64.zero false) f1e6))) =
      (.ok (n % 1000000) : Py Int) := by
  have h0 : 0 ≤ n % 1000000 := Int.emod_nonneg _ (by decide)
  have h1 : n % 1000000 < 1000000 := Int.emod_lt_of_pos _ (by decide)
  have hb : (n % 1000000).natAbs < 2 ^ 53 := by omega
  rw [tdToFloat_small hb, mul_zero_f1e6]
  obtain ⟨hf, hv⟩ := add_ofInt_zero hb
  exact round_int_value hf hv hb

/-- `deltaNumPy` with int arguments is the int-only model `deltaPy`, whose twin agreement and
exactness are `TimedeltaCtorTwins` and `TimedeltaCtorExact`: on ints the type loop passes, the
float branches (:692-698, :708-713, :732-737) are not taken, and `round(microseconds +
usdouble)` (:744) adds `0.0 * 1e6` to an int below `10**6`, which `round` gives back. -/
theorem timedeltaNumPyInt_proven : TimedeltaNumPyInt := by
  intro days seconds microseconds milliseconds minutes hours weeks
  have hr := round_mod (microseconds + milliseconds * 1000)
  simp only [bind, Except.bind] at hr
  simp only [deltaNumPy, deltaPy, tdTypeCheckPy, tdMul, tdAdd, tdDaysSplitPy, tdSecondsSplitPy, tdMicroPy, bind,
    Except.bind, pure, Except.pure]
  split at hr
  · cases hr
  · rename_i x hx
    rw [hr]
    simp only [Int.add_assoc]
    rfl

/-! ### Ints and integral-valued floats -/

/-- A finite double with an integer value. -/
def IntF (x : F64) (n : Int) : Prop := x.isFinite = true ∧ x.toRat = n

/-- A `timedelta` argument whose value is the integer `n`: an int, or a float with that exact
value. -/
def TdNum.Rep : TdNum → Int → Prop
  | .int m, n => m = n
  | .float x, n => IntF x n
  | .other _, _ => False

/-- An argument that may be omitted (`0` in Python, nothing accumulated in C). -/
def RepOpt : Option TdNum → Int → Prop
  | none, n => n = 0
  | some a, n => a.Rep n

theorem rat_int_add (a b : Int) : ((a : Rat) + (b : Rat)) = ((a + b : Int) : Rat) := (Rat.intCast_add a b).symm
theorem rat_int_mul (a b : Int) : ((a : Rat) * (b : Rat)) = ((a * b : Int) : Rat) := (Rat.intCast_mul a b).symm

theorem ofRat_int {n : Int} (hb : n.natAbs < 2 ^ 53) : IntF (F64.ofRat (n : Rat)) n := ofInt_small hb

theorem add_intF {x y : F64} {a b : Int} (hx : IntF x a) (hy : IntF y b) (hb : (a + b).natAbs < 2 ^ 53) :
    IntF (F64.add x y) (a + b) := by
  rw [IntF, add_of_finite hx.1 hy.1, hx.2, hy.2, rat_int_add]
  split
  · rename_i h0
    exact ⟨zero_isFinite _, by rw [zero_toRat, h0]⟩
  · exact ofRat_int hb

theorem mul_intF {x y : F64} {a b : Int} (hx : IntF x a) (hy : IntF y b) (hb : (a * b).natAbs < 2 ^ 53) :
    IntF (F64.mul x y) (a * b) := by
  rw [IntF, mul_of_finite hx.1 hy.1, hx.2, hy.2, rat_int_mul]
  split
  · rename_i h0
    exact ⟨zero_isFinite _, by rw [zero_toRat, h0]⟩
  · exact ofRat_int hb

theorem zero_intF (s : Bool) : IntF (F64.zero s) 0 := ⟨zero_isFinite s, zero_toRat s⟩

theorem trunc_intF {x : F64} {n : Int} (hx : IntF x n) : IntF (F64.trunc x) n := by
  have hn := isNaN_false_of_finite hx.1
  by_cases hz : x.isZero = true
  · have e : F64.trunc x = x := by simp [F64.trunc, hn, hx.1, hz]
    rw [e]; exact hx
  · have hz' : x.isZero = false := by simpa using hz
    have e : F64.trunc x = F64.ofIntS x.sign x.truncInt := by simp [F64.trunc, hn, hx.1, hz']
    rw [e, truncInt_of_int hx.2]
    exact ofIntS_value x.sign hx.1 hz' (Or.inl hx.2)

/-- `modf` of an integral double: a zero fractional part with the sign of `x`, and `x`'s value. -/
theorem modf_intF {x : F64} {n : Int} (hx : IntF x n) :
    (modfF x).1 = F64.zero x.sign ∧ IntF (modfF x).2 n := by
  have hn := isNaN_false_of_finite hx.1
  have hi := isInf_false_of_finite hx.1
  have ht := trunc_intF hx
  have hnf : (F64.trunc x).neg.isFinite = true := by rw [neg_isFinite]; exact ht.1
  have hsub : (F64.sub x (F64.trunc x)).isZero = true := by
    unfold F64.sub
    rw [add_of_finite hx.1 hnf, toRat_neg, hx.2, ht.2]
    simp only [Rat.add_neg_cancel, ite_true]
    exact zero_isZero _
  simp only [modfF, hn, hi, Bool.false_eq_true, ite_false, hsub, ite_true, true_and]
  exact ht

theorem fromDouble_intF {y : F64} {n : Int} (hy : IntF y n) : PyLong_FromDouble y = .ok n := by
  simp [PyLong_FromDouble, isInf_false_of_finite hy.1, isNaN_false_of_finite hy.1, truncInt_of_int hy.2]

theorem f86400_intF : IntF f86400 86400 := by unfold IntF; decide +kernel
theorem f1e6_intF : IntF f1e6 1000000 := by unfold IntF; decide +kernel

theorem tdToFloat_intF {n : Int} (hb : n.natAbs < 2 ^ 53) : ∃ y, tdToFloat n = .ok y ∧ IntF y n :=
  ⟨_, tdToFloat_small hb, ofInt_small hb⟩

theorem tdMul_rep {a : TdNum} {n k : Int} (h : a.Rep n) (hk : k.natAbs < 2 ^ 53) (hb : (n * k).natAbs < 2 ^ 53) :
    ∃ b, tdMul a k = .ok b ∧ b.Rep (n * k) := by
  cases a with
  | int m => exact ⟨_, rfl, by simp only [TdNum.Rep] at h ⊢; rw [h]⟩
  | float x =>
    obtain ⟨y, hy, hyv⟩ := tdToFloat_intF hk
    exact ⟨.float (F64.mul x y), by simp [tdMul, hy, bind, Except.bind, pure, Except.pure], mul_intF h hyv hb⟩
  | other _ => exact absurd h id

theorem tdAdd_rep {a b : TdNum} {m n : Int} (ha : a.Rep m) (hb : b.Rep n) (hm : m.natAbs < 2 ^ 53)
    (hn : n.natAbs < 2 ^ 53) (hs : (m + n).natAbs < 2 ^ 53) :
    ∃ c, tdAdd a b = .ok c ∧ c.Rep (m + n) := by
  cases a with
  | int p =>
    simp only [TdNum.Rep] at ha; subst ha
    cases b with
    | int q => simp only [TdNum.Rep] at hb; subst hb; exact ⟨_, rfl, rfl⟩
    | float y =>
      obtain ⟨z, hz, hzv⟩ := tdToFloat_intF hm
      exact ⟨.float (F64.add z y), by simp [tdAdd, hz, bind, Except.bind, pure, Except.pure], add_intF hzv hb hs⟩
    | other _ => exact absurd hb id
  | float x =>
    cases b with
    | int q =>
      simp only [TdNum.Rep] at hb; subst hb
      obtain ⟨z, hz, hzv⟩ := tdToFloat_intF hn
      exact ⟨.float (F64.add x z), by simp [tdAdd, hz, bind, Except.bind, pure, Except.pure], add_intF ha hzv hs⟩
    | float y => exact ⟨_, rfl, add_intF ha hb hs⟩
    | other _ => exact absurd hb id
  | other _ => exact absurd ha id

theorem daysSplit_rep {c : TdNum} {n : Int} (h : c.Rep n) :
    ∃ z, IntF z 0 ∧ tdDaysSplitPy c = .ok (n, 0, z) := by
  cases c with
  | int m => simp only [TdNum.Rep] at h; subst h; exact ⟨_, zero_intF false, rfl⟩
  | float x =>
    obtain ⟨e1, h2⟩ := modf_intF h
    have hm : IntF (F64.mul (modfF x).1 f86400) 0 := by
      rw [e1]; have := mul_intF (zero_intF x.sign) f86400_intF (by decide); simpa using this
    obtain ⟨e3, h4⟩ := modf_intF hm
    refine ⟨(modfF (F64.mul (modfF x).1 f86400)).1, by rw [e3]; exact zero_intF _, ?_⟩
    simp only [tdDaysSplitPy, fromDouble_intF h4, fromDouble_intF h2, bind, Except.bind, pure, Except.pure]
  | other _ => exact absurd h id

theorem secondsSplit_rep {c : TdNum} {n : Int} {z : F64} (hz : IntF z 0) (h : c.Rep n) :
    ∃ z', IntF z' 0 ∧ tdSecondsSplitPy z c = .ok (n, z') := by
  cases c with
  | int m => simp only [TdNum.Rep] at h; subst h; exact ⟨_, hz, rfl⟩
  | float x =>
    obtain ⟨e1, h2⟩ := modf_intF h
    refine ⟨F64.add (modfF x).1 z, ?_, ?_⟩
    · rw [e1]; have := add_intF (zero_intF x.sign) hz (by decide); simpa using this
    · simp only [tdSecondsSplitPy, fromDouble_intF h2, bind, Except.bind, pure, Except.pure]
  | other _ => exact absurd h id

theorem micro_rep {c : TdNum} {n d s : Int} {u : F64} (hu : IntF u 0) (h : c.Rep n) (hb : n.natAbs < 2 ^ 53) :
    tdMicroPy d s u c = .ok (d + n / 1000000 / 86400, s + n / 1000000 % 86400, n % 1000000) := by
  cases c with
  | int m =>
    simp only [TdNum.Rep] at h; subst h
    have h0 : 0 ≤ m % 1000000 := Int.emod_nonneg _ (by decide)
    have h1 : m % 1000000 < 1000000 := Int.emod_lt_of_pos _ (by decide)
    have hb' : (m % 1000000).natAbs < 2 ^ 53 := by omega
    have ha := add_intF (ofInt_small hb') hu (by simpa using hb')
    rw [Int.add_zero] at ha
    simp only [tdMicroPy, tdToFloat_small hb', bind, Except.bind, round_int_value ha.1 ha.2 hb', pure,
      Except.pure]
  | float x =>
    have ha := add_intF h hu (by simpa using hb)
    rw [Int.add_zero] at ha
    simp only [tdMicroPy, round_int_value ha.1 ha.2 hb, bind, Except.bind, pure, Except.pure]
  | other _ => exact absurd h id

/-- The bound of the narrowed twin: every argument below `2**31` in magnitude, so that every
product and sum Python forms in floating point (`weeks*7`, `minutes*60 + hours*3600`,
`milliseconds*1000` and the additions, all below `2**53`) is exact. -/
def Small31 (n : Int) : Prop := n.natAbs < 2 ^ 31

theorem typeCheck_rep (a1 a2 a3 a4 a5 a6 a7 : TdNum) (d1 d2 d3 d4 d5 d6 d7 : Int)
    (r1 : a1.Rep d1) (r2 : a2.Rep d2) (r3 : a3.Rep d3) (r4 : a4.Rep d4) (r5 : a5.Rep d5) (r6 : a6.Rep d6)
    (r7 : a7.Rep d7) :
    tdTypeCheckPy [("days", a1), ("seconds", a2), ("microseconds", a3), ("milliseconds", a4),
      ("minutes", a5), ("hours", a6), ("weeks", a7)] = .ok () := by
  have nother : ∀ (a : TdNum) (n : Int), a.Rep n → ∀ l, tdTypeCheckPy l = .ok () →
      ∀ name, tdTypeCheckPy ((name, a) :: l) = .ok () := by
    intro a n h l hl name
    cases a with
    | int _ => exact hl
    | float _ => exact hl
    | other _ => exact absurd h id
  exact nother _ _ r1 _ (nother _ _ r2 _ (nother _ _ r3 _ (nother _ _ r4 _ (nother _ _ r5 _
    (nother _ _ r6 _ (nother _ _ r7 _ rfl _) _) _) _) _) _) _

/-- `deltaNumPy` on ints and integral floats below `2**31` is the int model of their values. -/
theorem deltaNumPy_rep (a1 a2 a3 a4 a5 a6 a7 : TdNum) (days seconds microseconds milliseconds minutes hours weeks : Int)
    (r1 : a1.Rep days) (r2 : a2.Rep seconds) (r3 : a3.Rep microseconds) (r4 : a4.Rep milliseconds)
    (r5 : a5.Rep minutes) (r6 : a6.Rep hours) (r7 : a7.Rep weeks)
    (b1 : Small31 days) (b2 : Small31 seconds) (b3 : Small31 microseconds) (b4 : Small31 milliseconds)
    (b5 : Small31 minutes) (b6 : Small31 hours) (b7 : Small31 weeks) :
    deltaNumPy a1 a2 a3 a4 a5 a6 a7 = deltaPy days seconds microseconds milliseconds minutes hours weeks := by
  unfold Small31 at *
  have hc := typeCheck_rep a1 a2 a3 a4 a5 a6 a7 _ _ _ _ _ _ _ r1 r2 r3 r4 r5 r6 r7
  obtain ⟨w7, hw, rw7⟩ := tdMul_rep (k := 7) r7 (by decide) (by omega)
  obtain ⟨dd, hd, rdd⟩ := tdAdd_rep r1 rw7 (by omega) (by omega) (by omega)
  obtain ⟨m60, hm60, rm60⟩ := tdMul_rep (k := 60) r5 (by decide) (by omega)
  obtain ⟨h36, hh36, rh36⟩ := tdMul_rep (k := 3600) r6 (by decide) (by omega)
  obtain ⟨mh, hmh, rmh⟩ := tdAdd_rep rm60 rh36 (by omega) (by omega) (by omega)
  obtain ⟨ss, hss, rss⟩ := tdAdd_rep r2 rmh (by omega) (by omega) (by omega)
  obtain ⟨ms, hms, rms⟩ := tdMul_rep (k := 1000) r4 (by decide) (by omega)
  obtain ⟨uu, huu, ruu⟩ := tdAdd_rep r3 rms (by omega) (by omega) (by omega)
  obtain ⟨z, hz, hds⟩ := daysSplit_rep rdd
  obtain ⟨z', hz', hsec⟩ := secondsSplit_rep hz rss
  have hu : IntF (F64.mul z' f1e6) 0 := by have := mul_intF hz' f1e6_intF (by decide); simpa using this
  have hmic := micro_rep (d := days + weeks * 7 + (seconds + (minutes * 60 + hours * 3600)) / 86400)
    (s := 0 + (seconds + (minutes * 60 + hours * 3600)) % 86400) hu ruu (by omega)
  simp only [deltaNumPy, hc, hw, hd, hm60, hh36, hmh, hss, hms, huu, hds, hsec, hmic, deltaPy, bind, Except.bind,
    pure, Except.pure]
  simp only [Int.add_assoc]
  rfl

/-- `accum` on an int or an integral float adds `n * factor` exactly and leaves `leftover`
alone (`modf` gives a zero fractional part, so the `fracpart == 0.0` early return is taken). -/
theorem accumC_rep {v : TdNum} {n : Int} (tag : String) (sofar factor : Int) (lo : F64) (h : v.Rep n) :
    accumC tag sofar v factor lo = .ok (sofar + n * factor, lo) := by
  cases v with
  | int m => simp only [TdNum.Rep] at h; subst h; rfl
  | float x =>
    obtain ⟨e1, h2⟩ := modf_intF h
    have heq : F64.eq (modfF x).1 (F64.zero false) = true := by
      rw [e1, eq_of_finite (zero_isFinite _) (zero_isFinite _), zero_toRat, zero_toRat]; rfl
    simp only [accumC, fromDouble_intF h2, heq, bind, Except.bind, pure, Except.pure, ite_true]
  | other _ => exact absurd h id

/-- `deltaNumC` on ints and integral floats (any size) is the int model of their values. -/
theorem deltaNumC_rep (a1 a2 a3 a4 a5 a6 a7 : Option TdNum) (days seconds microseconds milliseconds minutes hours weeks : Int)
    (r1 : RepOpt a1 days) (r2 : RepOpt a2 seconds) (r3 : RepOpt a3 microseconds) (r4 : RepOpt a4 milliseconds)
    (r5 : RepOpt a5 minutes) (r6 : RepOpt a6 hours) (r7 : RepOpt a7 weeks) :
    deltaNumC a1 a2 a3 a4 a5 a6 a7 = deltaC days seconds microseconds milliseconds minutes hours weeks := by
  have hne : F64.ne (F64.zero false) (F64.zero false) = false := by decide +kernel
  have st : ∀ (tag : String) (factor : Int) (a : Option TdNum) (n : Int), RepOpt a n → ∀ acc : Int,
      tdAccumStepC (acc, F64.zero false) (a, tag, factor) = .ok (acc + n * factor, F64.zero false) := by
    intro tag factor a n h acc
    cases a with
    | none => simp only [RepOpt] at h; subst h; simp [tdAccumStepC]
    | some v => exact accumC_rep tag acc factor _ h
  unfold deltaNumC
  simp only [List.foldlM, bind, Except.bind]
  rw [st _ _ _ _ r3]; dsimp only
  rw [st _ _ _ _ r4]; dsimp only
  rw [st _ _ _ _ r2]; dsimp only
  rw [st _ _ _ _ r5]; dsimp only
  rw [st _ _ _ _ r6]; dsimp only
  rw [st _ _ _ _ r1]; dsimp only
  rw [st _ _ _ _ r7]
  simp only [pure, Except.pure]
  rw [hne]
  simp only [Bool.false_eq_true, ite_false]
  unfold deltaC
  apply congrArg usToDeltaC
  omega

/-- The narrowed float twin: for every combination of ints, integral-valued floats and (in C)
omitted arguments, each below `2**31` in magnitude, `timedelta(...)` agrees between the twins
and is the int model of the values (so `TimedeltaCtorExact` gives its value). Excluded, and on
record through the refuted `TimedeltaFloatCtorTwins`: fractional floats, where Python rounds
`hours*3600` and friends as doubles (gh-160806), and integral floats large enough that those
products or sums are inexact. -/
def TimedeltaIntegralFloatTwins : Prop :=
  ∀ (a1 a2 a3 a4 a5 a6 a7 : Option TdNum) (days seconds microseconds milliseconds minutes hours weeks : Int),
    RepOpt a1 days → RepOpt a2 seconds → RepOpt a3 microseconds → RepOpt a4 milliseconds →
    RepOpt a5 minutes → RepOpt a6 hours → RepOpt a7 weeks →
    Small31 days → Small31 seconds → Small31 microseconds → Small31 milliseconds →
    Small31 minutes → Small31 hours → Small31 weeks →
    deltaNumPy (a1.getD (.int 0)) (a2.getD (.int 0)) (a3.getD (.int 0)) (a4.getD (.int 0)) (a5.getD (.int 0))
        (a6.getD (.int 0)) (a7.getD (.int 0)) = deltaPy days seconds microseconds milliseconds minutes hours weeks ∧
    deltaNumC a1 a2 a3 a4 a5 a6 a7 = deltaC days seconds microseconds milliseconds minutes hours weeks ∧
    SameOutcome
      (deltaNumPy (a1.getD (.int 0)) (a2.getD (.int 0)) (a3.getD (.int 0)) (a4.getD (.int 0)) (a5.getD (.int 0))
        (a6.getD (.int 0)) (a7.getD (.int 0)))
      (deltaNumC a1 a2 a3 a4 a5 a6 a7)

theorem repOpt_getD {a : Option TdNum} {n : Int} (h : RepOpt a n) : (a.getD (.int 0)).Rep n := by
  cases a with
  | none => simp only [RepOpt] at h; subst h; rfl
  | some v => exact h

theorem timedeltaIntegralFloatTwins_proven : TimedeltaIntegralFloatTwins := by
  intro a1 a2 a3 a4 a5 a6 a7 days seconds microseconds milliseconds minutes hours weeks r1 r2 r3 r4 r5 r6 r7
    b1 b2 b3 b4 b5 b6 b7
  have hp := deltaNumPy_rep _ _ _ _ _ _ _ _ _ _ _ _ _ _ (repOpt_getD r1) (repOpt_getD r2) (repOpt_getD r3)
    (repOpt_getD r4) (repOpt_getD r5) (repOpt_getD r6) (repOpt_getD r7) b1 b2 b3 b4 b5 b6 b7
  have hc := deltaNumC_rep _ _ _ _ _ _ _ _ _ _ _ _ _ _ r1 r2 r3 r4 r5 r6 r7
  refine ⟨hp, hc, ?_⟩
  rw [hp, hc]
  exact timedeltaCtorTwins_proven _ _ _ _ _ _ _

end PyLean.Datetime
