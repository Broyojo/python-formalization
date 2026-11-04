import PyLean.Datetime.TimeProps

/-!
`datetime` arithmetic in both twins: `+`, `-`, comparison, hash, time tuples and
`fromutc`. The two implementations compute very differently (Python through
`timedelta`, C by normalizing the fields), so the proofs go through the total
number of microseconds.
-/

namespace PyLean.Datetime

open PyLean

/-! ### Canonical `timedelta` -/

/-- The normalized fields of `T` microseconds. -/
def canon (T : Int) : Delta := ⟨T / 86400000000, T / 1000000 % 86400, T % 1000000⟩

theorem canon_valid (T : Int) (h1 : MIN_US ≤ T) (h2 : T < END_US) : (canon T).Valid := by
  unfold canon Delta.Valid MAX_DELTA_DAYS
  unfold MIN_US END_US at *
  simp only
  omega

theorem canon_toUs (T : Int) : (canon T).toUs = T := by
  unfold canon Delta.toUs
  simp only
  omega

theorem mkDeltaPy_in (T : Int) (h1 : MIN_US ≤ T) (h2 : T < END_US) : mkDeltaPy T = .ok (canon T) := by
  unfold mkDeltaPy canon
  unfold MIN_US END_US at *
  rw [if_neg (by omega)]

theorem mkDeltaN_in (T : Int) (h1 : MIN_US ≤ T) (h2 : T < END_US) : mkDeltaN T = .ok (canon T) := by
  unfold mkDeltaN canon MAX_DELTA_DAYS
  unfold MIN_US END_US at *
  rw [if_pos (by omega)]

theorem addPy_eq (a b : Delta) : a.addPy b = mkDeltaPy (a.toUs + b.toUs) := by
  unfold Delta.addPy
  rw [deltaPy_eq]
  congr 1
  unfold totalUs Delta.toUs
  omega

theorem subPy_eq (a b : Delta) : a.subPy b = mkDeltaPy (a.toUs - b.toUs) := by
  unfold Delta.subPy
  rw [deltaPy_eq]
  congr 1
  unfold totalUs Delta.toUs
  omega

theorem subC_eq (a b : Delta) : a.subC b = mkDeltaN (a.toUs - b.toUs) := by
  unfold Delta.subC
  rw [newDeltaNormC_eq]
  congr 1
  unfold Delta.toUs
  omega

theorem negPy_eq (a : Delta) : a.negPy = mkDeltaPy (-a.toUs) := by
  unfold Delta.negPy
  rw [deltaPy_eq]
  congr 1
  unfold totalUs Delta.toUs
  omega

theorem ymd2ord_C (dt : DT) (h : dt.Valid) : ymdToOrdC dt.y dt.m dt.d = ymd2ord dt.y dt.m dt.d := by
  have := validDate_pos _ _ _ h.1
  exact ymdToOrdC_eq _ _ _ (by omega)

/-! ### `datetime - datetime` -/

/-- Microseconds of the naive fields since `0001-01-00`. -/
def DT.totalUs (dt : DT) : Int :=
  (ymd2ord dt.y dt.m dt.d * 86400 + (dt.h * 3600 + dt.mi * 60 + dt.s)) * 1000000 + dt.us

theorem totalUs_bounds (dt : DT) (h : dt.Valid) :
    86400000000 ≤ dt.totalUs ∧ dt.totalUs < 3652060 * 86400000000 := by
  have r := ymd2ord_range _ _ _ h.1
  obtain ⟨_, h1, h2, h3, h4, h5, h6, h7, h8, _⟩ := h
  unfold MAXORDINAL at r
  unfold DT.totalUs
  omega

/-- `datetime - datetime`: the twins agree for all valid operands, whatever the
tzinfo: the same `timedelta`, or the same exception class. -/
def DatetimeSubTwins : Prop :=
  ∀ (env : TzEnv) (a b : DT), env.Valid → a.Valid → b.Valid →
    SameOutcome (dtSubPy env a b) (dtSubC env a b)

theorem dtSub_base (a b : DT) (ha : a.Valid) (hb : b.Valid) :
    deltaPy (toordinal a.y a.m a.d - toordinal b.y b.m b.d)
      (a.s + a.mi * 60 + a.h * 3600 - (b.s + b.mi * 60 + b.h * 3600)) (a.us - b.us) 0 0 0 0 =
      .ok (canon (a.totalUs - b.totalUs)) := by
  have ta := totalUs_bounds a ha
  have tb := totalUs_bounds b hb
  rw [deltaPy_eq]
  have : totalUs (toordinal a.y a.m a.d - toordinal b.y b.m b.d)
      (a.s + a.mi * 60 + a.h * 3600 - (b.s + b.mi * 60 + b.h * 3600)) (a.us - b.us) 0 0 0 0 =
      a.totalUs - b.totalUs := by
    unfold totalUs toordinal DT.totalUs; omega
  rw [this]
  exact mkDeltaPy_in _ (by unfold MIN_US; omega) (by unfold END_US; omega)

theorem dtSub_baseC (a b : DT) (ha : a.Valid) (hb : b.Valid) :
    newDeltaNormC (ymdToOrdC a.y a.m a.d - ymdToOrdC b.y b.m b.d)
      ((a.h - b.h) * 3600 + (a.mi - b.mi) * 60 + (a.s - b.s)) (a.us - b.us) =
      .ok (canon (a.totalUs - b.totalUs)) := by
  have ta := totalUs_bounds a ha
  have tb := totalUs_bounds b hb
  have ea := ymd2ord_C a ha
  have eb := ymd2ord_C b hb
  rw [newDeltaNormC_eq, ea, eb]
  have : ((ymd2ord a.y a.m a.d - ymd2ord b.y b.m b.d) * 86400 +
      ((a.h - b.h) * 3600 + (a.mi - b.mi) * 60 + (a.s - b.s))) * 1000000 + (a.us - b.us) =
      a.totalUs - b.totalUs := by
    unfold DT.totalUs; omega
  rw [this]
  exact mkDeltaN_in _ (by unfold MIN_US; omega) (by unfold END_US; omega)

theorem dt_offset_valid (env : TzEnv) (henv : env.Valid) (a : DT) (h : OptTzOk a.tz) (o : Delta)
    (ho : a.utcoffsetPy env = .ok (some o)) : o.Valid := by
  unfold DT.utcoffsetPy at ho
  split at ho
  · cases ho
  · rename_i tz htz
    rw [htz] at h
    cases hr : tzUtcoffsetRaw env tz (some a) with
    | error e => rw [hr] at ho; cases ho
    | ok v =>
      rw [hr] at ho
      cases v with
      | none => cases ho
      | other ty => cases ho
      | delta d =>
        simp only [bind, Except.bind, checkUtcOffset] at ho
        split at ho
        · cases ho
        · cases ho; exact raw_off_valid env henv tz h _ o hr

theorem dt_offset_range (env : TzEnv) (henv : env.Valid) (a : DT) (h : OptTzOk a.tz) (o : Delta)
    (ho : a.utcoffsetPy env = .ok (some o)) : -86400000000 < o.toUs ∧ o.toUs < 86400000000 :=
  (datetimeOffsets_proven env a henv h).2.2 o ho

/-- The subtraction when tzinfo objects differ and both offsets are known. -/
theorem dtSub_aware (env : TzEnv) (a b : DT) (henv : env.Valid) (ha : a.Valid) (hb : b.Valid)
    (x y : Delta) (hs : sameTz a.tz b.tz = false)
    (h1 : a.utcoffsetPy env = .ok (some x)) (h2 : b.utcoffsetPy env = .ok (some y)) :
    dtSubPy env a b = .ok (canon (a.totalUs - b.totalUs + (y.toUs - x.toUs))) ∧
    dtSubC env a b = .ok (canon (a.totalUs - b.totalUs + (y.toUs - x.toUs))) := by
  have hax : OptTzOk a.tz := ha.2.2.2.2.2.2.2.2.2.2
  have hby : OptTzOk b.tz := hb.2.2.2.2.2.2.2.2.2.2
  have vx := dt_offset_valid env henv a hax x h1
  have vy := dt_offset_valid env henv b hby y h2
  have rx := dt_offset_range env henv a hax x h1
  have ry := dt_offset_range env henv b hby y h2
  have ta := totalUs_bounds a ha
  have tb := totalUs_bounds b hb
  have h1c := h1
  have h2c := h2
  rw [dt_utcoffset_twin env henv a hax] at h1c
  rw [dt_utcoffset_twin env henv b hby] at h2c
  have ecmp := delta_cmp_eq x y vx vy
  by_cases hxy : x = y
  · subst hxy
    have ez : a.totalUs - b.totalUs + (x.toUs - x.toUs) = a.totalUs - b.totalUs := by omega
    rw [ez]
    have hc0 : x.cmpC x = 0 := ecmp.2.1.mpr rfl
    constructor
    · simp [dtSubPy, dtSub_base a b ha hb, hs, h1, h2, offEq, bind, Except.bind, pure, Except.pure]
    · simp [dtSubC, dtSub_baseC a b ha hb, hs, h1c, h2c, hc0, bind, Except.bind, pure, Except.pure]
  · have hne : x.toUs ≠ y.toUs := by
      intro e
      apply hxy
      unfold Delta.Valid MAX_DELTA_DAYS at vx vy
      unfold Delta.toUs at e
      obtain ⟨d1, s1, u1⟩ := x
      obtain ⟨d2, s2, u2⟩ := y
      simp only at vx vy e
      have e1 : d1 = d2 := by omega
      have e2 : s1 = s2 := by omega
      have e3 : u1 = u2 := by omega
      rw [e1, e2, e3]
    have hc : x.cmpC y ≠ 0 := fun e => hne (ecmp.2.1.mp e)
    have hbe : (x == y) = false := by simp [hxy]
    constructor
    · have e1 : (canon (a.totalUs - b.totalUs)).addPy y = .ok (canon (a.totalUs - b.totalUs + y.toUs)) := by
        rw [addPy_eq, canon_toUs]
        exact mkDeltaPy_in _ (by unfold MIN_US; omega) (by unfold END_US; omega)
      have e2 : (canon (a.totalUs - b.totalUs + y.toUs)).subPy x =
          .ok (canon (a.totalUs - b.totalUs + (y.toUs - x.toUs))) := by
        rw [subPy_eq, canon_toUs]
        have : a.totalUs - b.totalUs + y.toUs - x.toUs = a.totalUs - b.totalUs + (y.toUs - x.toUs) := by omega
        rw [this]
        exact mkDeltaPy_in _ (by unfold MIN_US; omega) (by unfold END_US; omega)
      simp [dtSubPy, dtSub_base a b ha hb, hs, h1, h2, offEq, hbe, bind, Except.bind, e1, e2]
    · have e1 : x.subC y = .ok (canon (x.toUs - y.toUs)) := by
        rw [subC_eq]
        exact mkDeltaN_in _ (by unfold MIN_US; omega) (by unfold END_US; omega)
      have e2 : (canon (a.totalUs - b.totalUs)).subC (canon (x.toUs - y.toUs)) =
          .ok (canon (a.totalUs - b.totalUs + (y.toUs - x.toUs))) := by
        rw [subC_eq, canon_toUs, canon_toUs]
        have : a.totalUs - b.totalUs - (x.toUs - y.toUs) = a.totalUs - b.totalUs + (y.toUs - x.toUs) := by omega
        rw [this]
        exact mkDeltaN_in _ (by unfold MIN_US; omega) (by unfold END_US; omega)
      simp [dtSubC, dtSub_baseC a b ha hb, hs, h1c, h2c, hc, bind, Except.bind, pure, Except.pure, e1, e2,
        Functor.map, Except.map]

theorem datetimeSubTwins_proven : DatetimeSubTwins := by
  intro env a b henv ha hb
  have hax : OptTzOk a.tz := ha.2.2.2.2.2.2.2.2.2.2
  have hby : OptTzOk b.tz := hb.2.2.2.2.2.2.2.2.2.2
  have tw1 := dt_utcoffset_twin env henv a hax
  have tw2 := dt_utcoffset_twin env henv b hby
  cases hs : sameTz a.tz b.tz with
  | true =>
    have e1 : dtSubPy env a b = .ok (canon (a.totalUs - b.totalUs)) := by
      simp [dtSubPy, dtSub_base a b ha hb, hs, bind, Except.bind, pure, Except.pure]
    have e2 : dtSubC env a b = .ok (canon (a.totalUs - b.totalUs)) := by
      simp [dtSubC, dtSub_baseC a b ha hb, hs, bind, Except.bind, pure, Except.pure]
    rw [e1, e2]
    exact sameOutcome_refl _
  | false =>
    cases h1 : a.utcoffsetPy env with
    | error e =>
      have h1c := h1
      rw [tw1] at h1c
      have e1 : dtSubPy env a b = .error e := by
        simp [dtSubPy, dtSub_base a b ha hb, hs, h1, bind, Except.bind]
      have e2 : dtSubC env a b = .error e := by
        simp [dtSubC, hs, h1c, bind, Except.bind]
      rw [e1, e2]
      exact sameOutcome_refl _
    | ok o1 =>
      cases h2 : b.utcoffsetPy env with
      | error e =>
        have h1c := h1
        have h2c := h2
        rw [tw1] at h1c
        rw [tw2] at h2c
        have e1 : dtSubPy env a b = .error e := by
          simp [dtSubPy, dtSub_base a b ha hb, hs, h1, h2, bind, Except.bind]
        have e2 : dtSubC env a b = .error e := by
          simp [dtSubC, hs, h1c, h2c, bind, Except.bind]
        rw [e1, e2]
        exact sameOutcome_refl _
      | ok o2 =>
        have h1c := h1
        have h2c := h2
        rw [tw1] at h1c
        rw [tw2] at h2c
        cases o1 with
        | none =>
          cases o2 with
          | none =>
            have e1 : dtSubPy env a b = .ok (canon (a.totalUs - b.totalUs)) := by
              simp [dtSubPy, dtSub_base a b ha hb, hs, h1, h2, offEq, bind, Except.bind, pure, Except.pure]
            have e2 : dtSubC env a b = .ok (canon (a.totalUs - b.totalUs)) := by
              simp [dtSubC, dtSub_baseC a b ha hb, hs, h1c, h2c, bind, Except.bind, pure, Except.pure]
            rw [e1, e2]
            exact sameOutcome_refl _
          | some y =>
            have e1 : dtSubPy env a b = .error (.typeError "cannot mix naive and timezone-aware time") := by
              simp [dtSubPy, dtSub_base a b ha hb, hs, h1, h2, offEq, bind, Except.bind, throw, throwThe,
                MonadExceptOf.throw]
            have e2 : dtSubC env a b = .error (.typeError "can't subtract offset-naive and offset-aware datetimes") := by
              simp [dtSubC, hs, h1c, h2c, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
            rw [e1, e2]
            rfl
        | some x =>
          cases o2 with
          | none =>
            have e1 : dtSubPy env a b = .error (.typeError "cannot mix naive and timezone-aware time") := by
              simp [dtSubPy, dtSub_base a b ha hb, hs, h1, h2, offEq, bind, Except.bind, throw, throwThe,
                MonadExceptOf.throw]
            have e2 : dtSubC env a b = .error (.typeError "can't subtract offset-naive and offset-aware datetimes") := by
              simp [dtSubC, hs, h1c, h2c, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
            rw [e1, e2]
            rfl
          | some y =>
            obtain ⟨e1, e2⟩ := dtSub_aware env a b henv ha hb x y hs h1 h2
            rw [e1, e2]
            exact sameOutcome_refl _

/-! ### `datetime + timedelta` -/

theorem np_us (hi lo : Int) : normalizePair hi lo 1000000 = (hi + lo / 1000000, lo % 1000000) := by
  rw [normalizePair_pos hi lo 1000000 (by decide)]; split
  · rfl
  · simp only [Prod.mk.injEq]; omega

theorem np_60 (hi lo : Int) : normalizePair hi lo 60 = (hi + lo / 60, lo % 60) := by
  rw [normalizePair_pos hi lo 60 (by decide)]; split
  · rfl
  · simp only [Prod.mk.injEq]; omega

theorem np_24 (hi lo : Int) : normalizePair hi lo 24 = (hi + lo / 24, lo % 24) := by
  rw [normalizePair_pos hi lo 24 (by decide)]; split
  · rfl
  · simp only [Prod.mk.injEq]; omega

/-- The `datetime` at `T` microseconds, with `fold=0`. -/
def dtFromTotal (T : Int) (tz : Option Tz) : DT :=
  let D := T / 86400000000
  let S := T / 1000000 % 86400
  let ymd := ord2ymd D
  ⟨ymd.1, ymd.2.1, ymd.2.2, S / 3600, S % 3600 / 60, S % 3600 % 60, T % 1000000, 0, tz⟩

theorem dtFromTotal_valid (T : Int) (tz : Option Tz) (h1 : 1 ≤ T / 86400000000)
    (h2 : T / 86400000000 ≤ MAXORDINAL) (htz : OptTzOk tz) : (dtFromTotal T tz).Valid := by
  obtain ⟨hv, -, -⟩ := ord2ymd_valid _ h1 h2
  unfold DT.Valid dtFromTotal
  simp only
  exact ⟨hv, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by simp, htz⟩

set_option maxHeartbeats 2000000 in
theorem norm_arith (ord hh mi s us dd ds du : Int) :
    ((ord + dd) * 86400000000 + (hh * 3600 + mi * 60 + (s + ds)) * 1000000 + (us + du)) / 86400000000 - ord =
        dd + (hh + (mi + (s + ds + (us + du) / 1000000) / 60) / 60) / 24 ∧
    ((ord + dd) * 86400000000 + (hh * 3600 + mi * 60 + (s + ds)) * 1000000 + (us + du)) / 1000000 % 86400 =
        (hh + (mi + (s + ds + (us + du) / 1000000) / 60) / 60) % 24 * 3600 +
        (mi + (s + ds + (us + du) / 1000000) / 60) % 60 * 60 + (s + ds + (us + du) / 1000000) % 60 ∧
    ((ord + dd) * 86400000000 + (hh * 3600 + mi * 60 + (s + ds)) * 1000000 + (us + du)) % 1000000 =
        (us + du) % 1000000 := by
  omega

theorem tmFromTotal_valid (T : Int) (tz : Option Tz) (htz : OptTzOk tz) :
    TM.Valid ⟨T / 1000000 % 86400 / 3600, T / 1000000 % 86400 % 3600 / 60, T / 1000000 % 86400 % 3600 % 60,
      T % 1000000, 0, tz⟩ := by
  unfold TM.Valid
  simp only
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by simp, htz⟩

attribute [local irreducible] normalizePair normalizeYMDC in
/-- `normalize_datetime` with the carries written out. -/
theorem normalizeDatetimeC_eq (y m d hh mi s us : Int) :
    normalizeDatetimeC y m d hh mi s us =
      normalizeTailC ((hh + (mi + (s + us / 1000000) / 60) / 60) % 24) ((mi + (s + us / 1000000) / 60) % 60)
        ((s + us / 1000000) % 60) (us % 1000000)
        (normalizeYMDC y m (d + (hh + (mi + (s + us / 1000000) / 60) / 60) / 24)) := by
  unfold normalizeDatetimeC normalizeDateC
  rw [np_us]
  dsimp only
  rw [np_60]
  dsimp only
  rw [np_60]
  dsimp only
  rw [np_24]

theorem norm_fields (T r1 r2 r3 : Int) (h : T / 1000000 % 86400 = r3 * 3600 + r2 * 60 + r1)
    (b1 : 0 ≤ r1 ∧ r1 < 60) (b2 : 0 ≤ r2 ∧ r2 < 60) (b3 : 0 ≤ r3 ∧ r3 < 24) :
    r1 = T / 1000000 % 86400 % 3600 % 60 ∧ r2 = T / 1000000 % 86400 % 3600 / 60 ∧
      r3 = T / 1000000 % 86400 / 3600 := by
  omega

/-- What the C normalization of a `datetime` computes. -/
theorem normalizeDatetimeC_spec (dt : DT) (hv : dt.Valid) (dd ds du T : Int)
    (hT : T = (ymd2ord dt.y dt.m dt.d + dd) * 86400000000 +
      (dt.h * 3600 + dt.mi * 60 + (dt.s + ds)) * 1000000 + (dt.us + du)) :
    (1 ≤ T / 86400000000 ∧ T / 86400000000 ≤ MAXORDINAL →
      normalizeDatetimeC dt.y dt.m (dt.d + dd) dt.h dt.mi (dt.s + ds) (dt.us + du) = .ok (dtFromTotal T none)) ∧
    (¬(1 ≤ T / 86400000000 ∧ T / 86400000000 ≤ MAXORDINAL) →
      (normalizeDatetimeC dt.y dt.m (dt.d + dd) dt.h dt.mi (dt.s + ds) (dt.us + du)).raises "OverflowError") := by
  obtain ⟨n1, n2, n3⟩ := norm_arith (ymd2ord dt.y dt.m dt.d) dt.h dt.mi dt.s dt.us dd ds du
  rw [← hT] at n1 n2 n3
  have m60 : ∀ a : Int, 0 ≤ a % 60 ∧ a % 60 < 60 := fun a => by omega
  have m24 : ∀ a : Int, 0 ≤ a % 24 ∧ a % 24 < 24 := fun a => by omega
  obtain ⟨e1, e2, e3⟩ := norm_fields T _ _ _ n2 (m60 _) (m60 _) (m24 _)
  rw [normalizeDatetimeC_eq, Int.add_assoc dt.d dd, ← n1, ← n3, e1, e2, e3]
  have hdate := hv.1
  generalize hD : T / 86400000000 - ymd2ord dt.y dt.m dt.d = D
  have hD' : T / 86400000000 = ymd2ord dt.y dt.m dt.d + D := by rw [← hD]; omega
  rw [hD']
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨y', m', d', hn, hv', ho⟩ := normalizeYMDC_ok dt.y dt.m dt.d ⟨D, 0, 0⟩ hdate h1 h2
    have hn' : normalizeYMDC dt.y dt.m (dt.d + D) = .ok (y', m', d') := hn
    rw [hn']
    unfold normalizeTailC
    have hrt := (ord_roundtrip y' m' d' (by have := validDate_pos _ _ _ hv'; omega)
      ⟨hv'.2.2.1, hv'.2.2.2.1⟩ ⟨hv'.2.2.2.2.1, hv'.2.2.2.2.2⟩).1
    have ho' : ymd2ord y' m' d' = ymd2ord dt.y dt.m dt.d + D := ho
    rw [ho'] at hrt
    simp only [dtFromTotal, hD', hrt]
  · intro hout
    obtain ⟨e, he, hc⟩ := normalizeYMDC_err dt.y dt.m dt.d ⟨D, 0, 0⟩ hdate hout
    have he' : normalizeYMDC dt.y dt.m (dt.d + D) = .error e := he
    rw [he']
    exact ⟨e, rfl, hc⟩

theorem addC_spec (dt : DT) (hv : dt.Valid) (t : Delta) (f : Int) (hf : f = 1 ∨ f = -1) :
    let T := dt.totalUs + f * t.toUs
    (1 ≤ T / 86400000000 ∧ T / 86400000000 ≤ MAXORDINAL →
      addDatetimeTimedeltaC dt t f = .ok (dtFromTotal T dt.tz)) ∧
    (¬(1 ≤ T / 86400000000 ∧ T / 86400000000 ≤ MAXORDINAL) →
      (addDatetimeTimedeltaC dt t f).raises "OverflowError") := by
  intro T
  have eT : T = (ymd2ord dt.y dt.m dt.d + t.days * f) * 86400000000 +
      (dt.h * 3600 + dt.mi * 60 + (dt.s + t.seconds * f)) * 1000000 + (dt.us + t.us * f) := by
    simp only [T]
    unfold DT.totalUs Delta.toUs
    rcases hf with rfl | rfl <;> omega
  obtain ⟨hs1, hs2⟩ := normalizeDatetimeC_spec dt hv (t.days * f) (t.seconds * f) (t.us * f) T eT
  constructor
  · intro hr
    have htz : OptTzOk dt.tz := hv.2.2.2.2.2.2.2.2.2.2
    unfold addDatetimeTimedeltaC
    simp only [hs1 hr, bind, Except.bind]
    have := newDT_ok (dtFromTotal T dt.tz) (dtFromTotal_valid T dt.tz hr.1 hr.2 htz)
    unfold dtFromTotal at this ⊢
    exact this
  · intro hr
    obtain ⟨e, he, hc⟩ := hs2 hr
    unfold addDatetimeTimedeltaC
    simp only [he, bind, Except.bind]
    exact ⟨e, rfl, hc⟩

theorem dtAddPy_spec (dt : DT) (hv : dt.Valid) (t : Delta) (ht : t.Valid) :
    let T := dt.totalUs + t.toUs
    (1 ≤ T / 86400000000 ∧ T / 86400000000 ≤ MAXORDINAL → dtAddPy dt t = .ok (dtFromTotal T dt.tz)) ∧
    (¬(1 ≤ T / 86400000000 ∧ T / 86400000000 ≤ MAXORDINAL) → (dtAddPy dt t).raises "OverflowError") := by
  intro T
  have b := totalUs_bounds dt hv
  have e0 : deltaPy (toordinal dt.y dt.m dt.d) dt.s dt.us 0 dt.mi dt.h 0 = .ok (canon dt.totalUs) := by
    rw [deltaPy_eq]
    have : totalUs (toordinal dt.y dt.m dt.d) dt.s dt.us 0 dt.mi dt.h 0 = dt.totalUs := by
      unfold totalUs toordinal DT.totalUs; omega
    rw [this]
    exact mkDeltaPy_in _ (by unfold MIN_US; omega) (by unfold END_US; omega)
  have e1 : (canon dt.totalUs).addPy t = mkDeltaPy T := by
    rw [addPy_eq, canon_toUs]
  unfold dtAddPy
  simp only [e0, bind, Except.bind, e1]
  have tb := toUs_valid_bounds t ht
  constructor
  · rintro ⟨h1, h2⟩
    have hT : MIN_US ≤ T ∧ T < END_US := by
      unfold MIN_US END_US MAXORDINAL at *
      omega
    rw [mkDeltaPy_in T hT.1 hT.2]
    dsimp only
    have hc : 0 < (canon T).days ∧ (canon T).days ≤ MAXORDINAL := ⟨by simp only [canon]; omega, h2⟩
    rw [if_pos hc]
    simp only [canon]
    obtain ⟨hvv, -, -⟩ := ord2ymd_valid _ h1 h2
    have htz : OptTzOk dt.tz := hv.2.2.2.2.2.2.2.2.2.2
    have hf := dtFromTotal_valid T dt.tz h1 h2 htz
    have etm := newTM_ok ⟨T / 1000000 % 86400 / 3600, T / 1000000 % 86400 % 3600 / 60, T / 1000000 % 86400 % 3600 % 60,
      T % 1000000, 0, dt.tz⟩ (tmFromTotal_valid T dt.tz htz)
    simp only [fromordinalPy, checkDate_ok _ _ _ hvv, etm, dtCombine, Option.getD_none]
    have := newDT_ok _ hf
    unfold dtFromTotal at this ⊢
    exact this
  · intro hout
    by_cases hT : MIN_US ≤ T ∧ T < END_US
    · rw [mkDeltaPy_in T hT.1 hT.2]
      dsimp only
      have hc : ¬ (0 < (canon T).days ∧ (canon T).days ≤ MAXORDINAL) := by simp only [canon]; omega
      rw [if_neg hc]
      exact ⟨_, rfl, rfl⟩
    · have hn : (T / 86400000000).natAbs > 999999999 := by
        unfold MIN_US END_US at hT; omega
      simp only [mkDeltaPy, hn, ite_true]
      exact ⟨_, rfl, rfl⟩

/-- `datetime + timedelta`: if the day of the result is in range, both twins return
the same `datetime` at the sum of the microseconds, with the same tzinfo and
`fold=0`; otherwise both raise `OverflowError`. -/
def DatetimeAddTimedelta : Prop :=
  ∀ (dt : DT) (t : Delta), dt.Valid → t.Valid →
    let T := dt.totalUs + t.toUs
    (1 ≤ T / 86400000000 ∧ T / 86400000000 ≤ MAXORDINAL →
      dtAddPy dt t = .ok (dtFromTotal T dt.tz) ∧ addDatetimeTimedeltaC dt t 1 = .ok (dtFromTotal T dt.tz)) ∧
    (¬(1 ≤ T / 86400000000 ∧ T / 86400000000 ≤ MAXORDINAL) →
      (dtAddPy dt t).raises "OverflowError" ∧ (addDatetimeTimedeltaC dt t 1).raises "OverflowError")

theorem datetimeAddTimedelta_proven : DatetimeAddTimedelta := by
  intro dt t hv ht T
  have p := dtAddPy_spec dt hv t ht
  have c := addC_spec dt hv t 1 (Or.inl rfl)
  simp only at p c
  have e : dt.totalUs + 1 * t.toUs = T := by simp only [T]; omega
  rw [e] at c
  exact ⟨fun h => ⟨p.1 h, c.1 h⟩, fun h => ⟨p.2 h, c.2 h⟩⟩

/-- `datetime - timedelta`: same statement with the difference. -/
def DatetimeSubTimedelta : Prop :=
  ∀ (dt : DT) (t : Delta), dt.Valid → t.Valid →
    let T := dt.totalUs - t.toUs
    (1 ≤ T / 86400000000 ∧ T / 86400000000 ≤ MAXORDINAL →
      dtSubDeltaPy dt t = .ok (dtFromTotal T dt.tz) ∧ addDatetimeTimedeltaC dt t (-1) = .ok (dtFromTotal T dt.tz)) ∧
    (¬(1 ≤ T / 86400000000 ∧ T / 86400000000 ≤ MAXORDINAL) →
      (dtSubDeltaPy dt t).raises "OverflowError" ∧ (addDatetimeTimedeltaC dt t (-1)).raises "OverflowError")

theorem datetimeSubTimedelta_proven : DatetimeSubTimedelta := by
  intro dt t hv ht T
  have c := addC_spec dt hv t (-1) (Or.inr rfl)
  simp only at c
  have e : dt.totalUs + -1 * t.toUs = T := by simp only [T]; omega
  rw [e] at c
  have b := totalUs_bounds dt hv
  have tb := toUs_valid_bounds t ht
  by_cases hn : MIN_US ≤ -t.toUs ∧ -t.toUs < END_US
  · have hneg : t.negPy = .ok (canon (-t.toUs)) := by rw [negPy_eq]; exact mkDeltaPy_in _ hn.1 hn.2
    have p := dtAddPy_spec dt hv (canon (-t.toUs)) (canon_valid _ hn.1 hn.2)
    simp only [canon_toUs] at p
    have e2 : dt.totalUs + -t.toUs = T := by simp only [T]; omega
    rw [e2] at p
    have hp : dtSubDeltaPy dt t = dtAddPy dt (canon (-t.toUs)) := by
      simp [dtSubDeltaPy, hneg, bind, Except.bind]
    rw [hp]
    exact ⟨fun h => ⟨p.1 h, c.1 h⟩, fun h => ⟨p.2 h, c.2 h⟩⟩
  · have hneg : t.negPy.raises "OverflowError" := by
      rw [negPy_eq]
      have := (mkDeltaPy_spec (-t.toUs)).2.2
      rcases this with ⟨r, hr⟩ | h
      · exact absurd ((mkDeltaPy_spec (-t.toUs)).2.1.mp ⟨r, hr⟩) hn
      · exact h
    have hout : ¬(1 ≤ T / 86400000000 ∧ T / 86400000000 ≤ MAXORDINAL) := by
      unfold MIN_US END_US MAXORDINAL at *
      omega
    obtain ⟨e', he, hc⟩ := hneg
    have hp : dtSubDeltaPy dt t = .error e' := by
      simp [dtSubDeltaPy, he, bind, Except.bind]
    refine ⟨fun h => absurd h hout, fun _ => ⟨⟨e', hp, hc⟩, c.2 hout⟩⟩

/-! ### Fixed offsets: `fromutc` -/

/-- `timezone.fromutc(dt)` is `dt + offset` in both twins, for a `dt` carrying this
`timezone`, and raises `ValueError` for any other `dt`. -/
def TimezoneFromutc : Prop :=
  ∀ (tz : Tz) (off : Delta) (dt : DT), off.Valid → dt.Valid →
    SameOutcome (timezoneFromutcPy tz off dt) (timezoneFromutcC tz off dt)

theorem timezoneFromutc_proven : TimezoneFromutc := by
  intro tz off dt hoff hv
  unfold timezoneFromutcPy timezoneFromutcC
  split
  · simp [SameOutcome, PyExc.className]
  · have h := datetimeAddTimedelta_proven dt off hv hoff
    simp only at h
    have e : (1 : Int) = 1 := rfl
    by_cases hr : 1 ≤ (dt.totalUs + off.toUs) / 86400000000 ∧ (dt.totalUs + off.toUs) / 86400000000 ≤ MAXORDINAL
    · obtain ⟨e1, e2⟩ := h.1 hr
      rw [e1, e2]
      exact sameOutcome_refl _
    · obtain ⟨⟨e1, h1, c1⟩, ⟨e2, h2, c2⟩⟩ := h.2 hr
      rw [h1, h2]
      simp only [SameOutcome]
      rw [c1, c2]

/-! ### Hash and comparison -/

/-- `hash(datetime)`: the twins hash the same key (the UTC value for an aware
`datetime`, the packed fields for a naive one), and `fold` plays no part. -/
def DatetimeHashTwins : Prop :=
  ∀ (env : TzEnv) (dt : DT), env.Valid → dt.Valid → SameOutcome (dtHashKeyPy env dt) (dtHashKeyC env dt)

theorem datetimeHashTwins_proven : DatetimeHashTwins := by
  intro env dt henv hv
  have htz : OptTzOk dt.tz := hv.2.2.2.2.2.2.2.2.2.2
  have hb := totalUs_bounds dt hv
  have eo := ymd2ord_C dt hv
  unfold dtHashKeyPy dtHashKeyC
  generalize ht : (if dt.fold ≠ 0 then { dt with fold := 0 } else dt) = t
  have htv : OptTzOk t.tz := by
    subst ht; split <;> exact htz
  dsimp only
  rw [dt_utcoffset_twin env henv t htv]
  cases ho : t.utcoffsetC env with
  | error e => exact sameOutcome_refl (.error e)
  | ok o =>
    cases o with
    | none =>
      have : dtData t = dtData dt := by subst ht; split <;> rfl
      simp only [bind, Except.bind, pure, Except.pure]
      rw [this]
      rfl
    | some x =>
      have hp : t.utcoffsetPy env = .ok (some x) := by
        rw [dt_utcoffset_twin env henv t htv]; exact ho
      have rx := dt_offset_range env henv t htv x hp
      have e1 : deltaPy (ymd2ord dt.y dt.m dt.d) (dt.h * 3600 + dt.mi * 60 + dt.s) dt.us 0 0 0 0 = .ok (canon dt.totalUs) := by
        rw [deltaPy_eq]
        have : totalUs (ymd2ord dt.y dt.m dt.d) (dt.h * 3600 + dt.mi * 60 + dt.s) dt.us 0 0 0 0 = dt.totalUs := by
          unfold totalUs DT.totalUs; omega
        rw [this]
        exact mkDeltaPy_in _ (by unfold MIN_US; omega) (by unfold END_US; omega)
      have e2 : newDeltaNormC (ymdToOrdC dt.y dt.m dt.d) (dt.h * 3600 + dt.mi * 60 + dt.s) dt.us = .ok (canon dt.totalUs) := by
        rw [newDeltaNormC_eq, eo]
        exact mkDeltaN_in _ (by unfold MIN_US DT.totalUs at *; omega) (by unfold END_US DT.totalUs at *; omega)
      have e3 : (canon dt.totalUs).subPy x = .ok (canon (dt.totalUs - x.toUs)) := by
        rw [subPy_eq, canon_toUs]
        exact mkDeltaPy_in _ (by unfold MIN_US; omega) (by unfold END_US; omega)
      have e4 : (canon dt.totalUs).subC x = .ok (canon (dt.totalUs - x.toUs)) := by
        rw [subC_eq, canon_toUs]
        exact mkDeltaN_in _ (by unfold MIN_US; omega) (by unfold END_US; omega)
      simp only [bind, Except.bind, pure, Except.pure, e1, e2, e3, e4]
      exact sameOutcome_refl _

/-! ### Time tuples -/

/-- `datetime.timetuple()`: the twins agree, with `tm_isdst` from `dst()`. -/
def DatetimeTimetuple : Prop :=
  ∀ (env : TzEnv) (dt : DT), env.Valid → dt.Valid → dtTimetuplePy env dt = dtTimetupleC env dt

theorem datetimeTimetuple_proven : DatetimeTimetuple := by
  intro env dt henv hv
  unfold dtTimetuplePy dtTimetupleC
  rw [dt_dst_twin env henv dt]
  cases dt.dstC env with
  | error e => rfl
  | ok o =>
    simp only [bind, Except.bind, pure, Except.pure]
    rw [buildStructTime_twins _ _ _ _ _ _ _ hv.1]

theorem dtFromTotal_self (dt : DT) (hv : dt.Valid) :
    let u := dtFromTotal dt.totalUs dt.tz
    u.y = dt.y ∧ u.m = dt.m ∧ u.d = dt.d ∧ u.h = dt.h ∧ u.mi = dt.mi ∧ u.s = dt.s := by
  intro u
  have pd := validDate_pos _ _ _ hv.1
  have hrt := (ord_roundtrip dt.y dt.m dt.d (by omega) ⟨hv.1.2.2.1, hv.1.2.2.2.1⟩
    ⟨hv.1.2.2.2.2.1, hv.1.2.2.2.2.2⟩).1
  obtain ⟨_, h1, h2, h3, h4, h5, h6, h7, h8, _⟩ := hv
  have eD : dt.totalUs / 86400000000 = ymd2ord dt.y dt.m dt.d := by unfold DT.totalUs; omega
  simp only [u, dtFromTotal, eD, hrt]
  unfold DT.totalUs
  simp only [true_and]
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- `datetime.utctimetuple()`: the twins agree on the tuple or on the exception
class; the tuple is the UTC value with `tm_isdst == 0`. -/
def DatetimeUtctimetuple : Prop :=
  ∀ (env : TzEnv) (dt : DT), env.Valid → dt.Valid →
    SameOutcome (dtUtctimetuplePy env dt) (dtUtctimetupleC env dt)

theorem datetimeUtctimetuple_proven : DatetimeUtctimetuple := by
  intro env dt henv hv
  have htz : OptTzOk dt.tz := hv.2.2.2.2.2.2.2.2.2.2
  unfold dtUtctimetuplePy dtUtctimetupleC
  rw [dt_utcoffset_twin env henv dt htz]
  cases ho : dt.utcoffsetC env with
  | error e => exact sameOutcome_refl (.error e)
  | ok o =>
    have hp : dt.utcoffsetPy env = .ok o := by rw [dt_utcoffset_twin env henv dt htz]; exact ho
    cases o with
    | none =>
      simp only [bind, Except.bind, pure, Except.pure]
      show buildStructTimePy _ _ _ _ _ _ _ = buildStructTimeC _ _ _ _ _ _ _
      exact buildStructTime_twins _ _ _ _ _ _ _ hv.1
    | some x =>
      have vx := dt_offset_valid env henv dt htz x hp
      have sub := datetimeSubTimedelta_proven dt x hv vx
      simp only at sub
      by_cases hz : x.bool = true
      · by_cases hr : 1 ≤ (dt.totalUs - x.toUs) / 86400000000 ∧ (dt.totalUs - x.toUs) / 86400000000 ≤ MAXORDINAL
        · obtain ⟨e1, e2⟩ := sub.1 hr
          have hvf := dtFromTotal_valid _ dt.tz hr.1 hr.2 htz
          simp only [hz, ite_true, e1, e2, bind, Except.bind, pure, Except.pure]
          show buildStructTimePy _ _ _ _ _ _ _ = buildStructTimeC _ _ _ _ _ _ _
          exact buildStructTime_twins _ _ _ _ _ _ _ hvf.1
        · obtain ⟨⟨e1, h1, c1⟩, ⟨e2, h2, c2⟩⟩ := sub.2 hr
          simp only [hz, ite_true, h1, h2, bind, Except.bind]
          simp only [SameOutcome]
          rw [c1, c2]
      · have h0 : x.toUs = 0 := by
          have := (timedeltaBoolHash_proven x x vx vx).1
          exact Classical.byContradiction (fun e => hz (this.mpr e))
        have b := totalUs_bounds dt hv
        have r := (dtFromTotal_self dt hv)
        simp only at r
        obtain ⟨r1, r2, r3, r4, r5, r6⟩ := r
        have hr : 1 ≤ (dt.totalUs - x.toUs) / 86400000000 ∧ (dt.totalUs - x.toUs) / 86400000000 ≤ MAXORDINAL := by
          rw [h0]; unfold MAXORDINAL; omega
        obtain ⟨-, e2⟩ := sub.1 hr
        simp only [hz, Bool.false_eq_true, ite_false, e2, bind, Except.bind, pure, Except.pure]
        have e0 : dt.totalUs - x.toUs = dt.totalUs := by omega
        rw [e0, r1, r2, r3, r4, r5, r6]
        show buildStructTimePy _ _ _ _ _ _ _ = buildStructTimeC _ _ _ _ _ _ _
        exact buildStructTime_twins _ _ _ _ _ _ _ hv.1

end PyLean.Datetime
