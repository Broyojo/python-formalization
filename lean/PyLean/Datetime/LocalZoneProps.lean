import PyLean.Datetime.LocalZone

/-!
Properties of `datetime._local_timezone` and `datetime.astimezone` with the local zone
(`LocalZone.lean`).
-/

namespace PyLean.Datetime
open PyLean

theorem ltFields_valid (ltz : Int → Py LocalTmZ) (hv : ∀ v r, ltz v = .ok r → LocalTmValid r.1) :
    ∀ v r, ltFields ltz v = .ok r → LocalTmValid r := by
  intro v r h
  unfold ltFields at h
  cases hz : ltz v with
  | error e => rw [hz] at h; cases h
  | ok x => rw [hz] at h; cases h; exact hv v x hz

theorem localPy_fits (lt : Int → Py LocalTm) (u v : Int) (h : localPy lt u = .ok v) : fitsTimeT u := by
  by_cases hf : fitsTimeT u
  · exact hf
  · simp [localPy, timeLocaltimePy, hf, bind, Except.bind, throw, throwThe, MonadExcept.throw,
      MonadExceptOf.throw] at h

/-- Every value `_mktime` returns was an argument of a successful `local(u)` call. -/
theorem mktimePy_fits (loc : Int → Py Int) (hl : ∀ u v, loc u = .ok v → fitsTimeT u) (t fold r : Int)
    (h : mktimePy loc t fold = .ok r) : fitsTimeT r := by
  unfold mktimePy at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  by_cases hf : fold = 0 <;> simp only [hf, ↓reduceIte, ite_true, ite_false] at h <;>
  · split at h
    · cases h
    · rename_i x h1
      split at h
      · cases h
      · rename_i t1 h2
        have f1 := hl _ _ h2
        split at h
        · split at h
          · cases h
          · rename_i z h3
            split at h
            · cases h; exact f1
            · split at h
              · cases h
              · rename_i w h4
                have f2 := hl _ _ h4
                split at h
                · cases h; exact f2
                · cases h; exact f1
        · simp only [Bool.false_eq_true, ↓reduceIte] at h
          split at h
          · cases h
          · rename_i w h4
            have f2 := hl _ _ h4
            split at h
            · cases h; exact f2
            · cases h
              unfold fitsTimeT at f1 f2 ⊢
              omega

theorem dtMktimePy_fits (lt : Int → Py LocalTm) (self : DT) (r : Int) (h : dtMktimePy lt self = .ok r) :
    fitsTimeT r :=
  mktimePy_fits (localPy lt) (fun u v hv => localPy_fits lt u v hv) _ _ r h

theorem localTimezoneTsPy_fits (lt : Int → Py LocalTm) (self : DT) (u r : Int) (hn : self.tz = none)
    (h : localTimezoneTsPy lt self u = .ok r) : fitsTimeT r := by
  unfold localTimezoneTsPy at h
  simp only [hn, Option.isNone_none, ↓reduceIte, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i a h1
    have fa := dtMktimePy_fits lt self a h1
    split at h
    · cases h
    · rename_i b h2
      have fb := dtMktimePy_fits lt _ b h2
      split at h
      · split at h
        · cases h; exact fb
        · cases h; exact fa
      · cases h; exact fa

/-- The zone of `localtime(ts)` agrees between the twins for every `ts` within `time_t`. -/
theorem localTzFromTs_twin (ltz : Int → Py LocalTmZ) (oid : Nat) (ts : Int) (hf : fitsTimeT ts) :
    SameOutcome (localTzFromTsPy ltz oid ts) (localTzFromTsC ltz oid ts) := by
  unfold localTzFromTsPy localTzFromTsC
  simp only [hf, not_true_eq_false, ↓reduceIte, bind, Except.bind]
  cases ltz ts with
  | error e => simp [SameOutcome]
  | ok r =>
    obtain ⟨_, g, z⟩ := r
    simp only
    rw [deltaPy_eq, newDeltaNormC_eq]
    have e : totalUs 0 g 0 0 0 0 0 = (0 * 86400 + g) * 1000000 + 0 := by unfold totalUs; omega
    rw [e]
    have hs := sameOutcome_mkN ((0 * 86400 + g) * 1000000 + 0)
    cases hp : mkDeltaPy ((0 * 86400 + g) * 1000000 + 0) with
    | error e1 =>
      cases hc : mkDeltaN ((0 * 86400 + g) * 1000000 + 0) with
      | error e2 => rw [hp, hc] at hs; simpa [SameOutcome] using hs
      | ok d => rw [hp, hc] at hs; cases hs
    | ok d =>
      cases hc : mkDeltaN ((0 * 86400 + g) * 1000000 + 0) with
      | error e2 => rw [hp, hc] at hs; cases hs
      | ok d' =>
        rw [hp, hc] at hs
        simp only [SameOutcome] at hs
        subst hs
        exact (timezoneNew_proven oid d (.str z) ((mkDeltaPy_spec _).1 d hp).1).1

/-- With `tm_gmtoff` strictly inside a day, the zone is `timezone(timedelta(seconds=gmtoff),
tm_zone)` with the new identity, in both twins. -/
theorem localTzFromTs_ok (ltz : Int → Py LocalTmZ) (oid : Nat) (ts : Int) (f : LocalTm) (g : Int) (z : String)
    (hf : fitsTimeT ts) (hl : ltz ts = .ok (f, g, z)) (h1 : -86400 < g) (h2 : g < 86400) :
    localTzFromTsPy ltz oid ts = .ok ⟨oid, .timezone (canon (g * 1000000)) (some z)⟩ ∧
    localTzFromTsC ltz oid ts = .ok ⟨oid, .timezone (canon (g * 1000000)) (some z)⟩ := by
  have hp : deltaPy 0 g 0 0 0 0 0 = .ok (canon (g * 1000000)) := by
    rw [deltaPy_eq]
    have e : totalUs 0 g 0 0 0 0 0 = g * 1000000 := by unfold totalUs; omega
    rw [e]; exact mkDeltaPy_in _ (by unfold MIN_US; omega) (by unfold END_US; omega)
  have hc : newDeltaNormC 0 g 0 = .ok (canon (g * 1000000)) := by
    rw [newDeltaNormC_eq]
    have e : (0 * 86400 + g) * 1000000 + 0 = g * 1000000 := by omega
    rw [e]; exact mkDeltaN_in _ (by unfold MIN_US; omega) (by unfold END_US; omega)
  have hu : (canon (g * 1000000)).toUs = g * 1000000 := canon_toUs _
  have hzp : timezoneNewPy oid (canon (g * 1000000)) (.str z) = .ok ⟨oid, .timezone (canon (g * 1000000)) (some z)⟩ := by
    simp only [timezoneNewPy, timezonePy, hu]
    by_cases h0 : g * 1000000 = 0
    · simp [h0]
    · have : -86399999999 ≤ g * 1000000 ∧ g * 1000000 ≤ 86399999999 := by omega
      simp [h0, this]
  have hzc : timezoneNewC oid (canon (g * 1000000)) (.str z) = .ok ⟨oid, .timezone (canon (g * 1000000)) (some z)⟩ := by
    have hs := (timezoneNew_proven oid (canon (g * 1000000)) (.str z)
      (canon_valid _ (by unfold MIN_US; omega) (by unfold END_US; omega))).1
    rw [hzp] at hs
    cases hzc : timezoneNewC oid (canon (g * 1000000)) (.str z) with
    | error e => rw [hzc] at hs; cases hs
    | ok v => rw [hzc] at hs; simp only [SameOutcome] at hs; rw [hs]
  refine ⟨?_, ?_⟩
  · simp [localTzFromTsPy, hf, hl, hp, hzp, bind, Except.bind]
  · simp [localTzFromTsC, hl, hc, hzc, bind, Except.bind]

theorem epochDT_valid : epochDT.Valid := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    Or.inl rfl, ?_⟩
  simp [epochDT, OptTzOk, Tz.Ok, tzUTC, Delta.Valid, MAX_DELTA_DAYS, Delta.toUs]

theorem epochDT_totalUs : epochDT.totalUs = epochC * 1000000 := by decide

theorem epochDT_utcoffset (env : TzEnv) : epochDT.utcoffsetPy env = .ok (some ⟨0, 0, 0⟩) := by
  simp [epochDT, DT.utcoffsetPy, tzUTC, tzUtcoffsetRaw, checkUtcOffset, bind, Except.bind]
  decide

/-- `datetime._local_timezone()` (Py:2121-2135) against C (`local_timezone_from_local`,
`local_timezone`, `local_timezone_from_timestamp`), for every valid datetime, every tzinfo
environment and every C-library `localtime` with fields a `datetime` accepts: a naive datetime
gets the same zone (or the same exception class) in both twins; an aware one with offset `o`
uses the UTC timestamp `floor((self - o - epoch) / 1 s)` (:2130); an aware one whose
`utcoffset()` is `None` raises `TypeError('cannot mix naive and timezone-aware time')` from
`self - _EPOCH`; and the zone of a timestamp is `timezone(timedelta(seconds=tm_gmtoff),
tm_zone)` with the new identity when `tm_gmtoff` is strictly inside a day (both twins), the
`localtime` exception otherwise propagated. Hypothesis (type invariant of the model): identity
0 is `timezone.utc` itself. -/
def LocalTimezoneFull : Prop :=
  ∀ (env : TzEnv) (ltz : Int → Py LocalTmZ) (oid : Nat) (self : DT),
    env.Valid → self.Valid → (∀ v r, ltz v = .ok r → LocalTmValid r.1) →
    (∀ z, self.tz = some z → z.oid = 0 → z = tzUTC) →
    (self.tz = none → SameOutcome (localTimezonePy env ltz oid self) (localTimezoneFromLocalC ltz oid self)) ∧
    (∀ o, self.tz ≠ none → self.utcoffsetPy env = .ok (some o) →
      localTimezonePy env ltz oid self = localTzFromTsPy ltz oid ((self.totalUs - o.toUs - epochC * 1000000) / 1000000)) ∧
    (self.tz ≠ none → self.utcoffsetPy env = .ok none →
      localTimezonePy env ltz oid self = .error (.typeError "cannot mix naive and timezone-aware time")) ∧
    (∀ ts f g z, fitsTimeT ts → ltz ts = .ok (f, g, z) → -86400 < g → g < 86400 →
      localTzFromTsPy ltz oid ts = .ok ⟨oid, .timezone (canon (g * 1000000)) (some z)⟩ ∧
      localTzFromTsC ltz oid ts = .ok ⟨oid, .timezone (canon (g * 1000000)) (some z)⟩) ∧
    (∀ ts e, fitsTimeT ts → ltz ts = .error e →
      localTzFromTsPy ltz oid ts = .error e ∧ localTzFromTsC ltz oid ts = .error e)

theorem localTimezoneFull_proven : LocalTimezoneFull := by
  intro env ltz oid self henv hv hlt hutc
  have hfv := ltFields_valid ltz hlt
  refine ⟨fun hn => ?_, fun o hn ho => ?_, fun hn ho => ?_, fun ts f g z hf hl h1 h2 => localTzFromTs_ok ltz oid ts f g z hf hl h1 h2,
    fun ts e hf hl => ?_⟩
  · have hself : ({ self with tz := none } : DT) = self := by cases self; simp_all
    unfold localTimezonePy localTimezoneFromLocalC
    rw [hself]
    simp only [hn, Option.isNone_none, ↓reduceIte]
    rw [← localTimezoneTwins_proven (ltFields ltz) self 0 hv hfv]
    cases hts : localTimezoneTsPy (ltFields ltz) self 0 with
    | error e => simp [bind, Except.bind, SameOutcome]
    | ok ts =>
      simp only [bind, Except.bind]
      exact localTzFromTs_twin ltz oid ts (localTimezoneTsPy_fits _ self 0 ts hn hts)
  · obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.mp hn
    have hsub : dtSubPy env self epochDT = .ok (canon (self.totalUs - epochDT.totalUs + (0 - o.toUs))) := by
      by_cases h0 : z.oid = 0
      · have hzu := hutc z hz h0
        have hs : sameTz self.tz epochDT.tz = true := by simp [sameTz, hz, epochDT, hzu]
        have ho0 : o = ⟨0, 0, 0⟩ := by
          have hraw : tzUtcoffsetRaw env tzUTC (some self) = .ok (.delta ⟨0, 0, 0⟩) := rfl
          have hchk : checkUtcOffset "utcoffset" (.delta ⟨0, 0, 0⟩) = .ok (some ⟨0, 0, 0⟩) := by decide
          unfold DT.utcoffsetPy at ho
          rw [hz, hzu] at ho
          simp only [hraw, hchk, bind, Except.bind, Except.ok.injEq, Option.some.injEq] at ho
          exact ho.symm
        subst ho0
        simp [dtSubPy, hs, dtSub_base self epochDT hv epochDT_valid, bind, Except.bind, pure, Except.pure,
          Delta.toUs]
      · have hs : sameTz self.tz epochDT.tz = false := by simp [sameTz, hz, epochDT, tzUTC, h0]
        have := (dtSub_aware env self epochDT henv hv epochDT_valid o ⟨0, 0, 0⟩ hs ho (epochDT_utcoffset env)).1
        rw [this]; rfl
    have hts : (canon (self.totalUs - epochDT.totalUs + (0 - o.toUs))).toUs / 1000000 =
        (self.totalUs - o.toUs - epochC * 1000000) / 1000000 := by
      rw [canon_toUs, epochDT_totalUs]; congr 1; omega
    unfold localTimezonePy
    simp only [hz, Option.isNone_some, Bool.false_eq_true, ↓reduceIte, hsub, bind, Except.bind, pure,
      Except.pure, hts]
  · obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.mp hn
    have hz0 : z.oid ≠ 0 := by
      intro h0
      have hzu := hutc z hz h0
      have hraw : tzUtcoffsetRaw env tzUTC (some self) = .ok (.delta ⟨0, 0, 0⟩) := rfl
      have hchk : checkUtcOffset "utcoffset" (.delta ⟨0, 0, 0⟩) = .ok (some ⟨0, 0, 0⟩) := by decide
      unfold DT.utcoffsetPy at ho
      rw [hz, hzu] at ho
      simp [hraw, hchk, bind, Except.bind] at ho
    have hs : sameTz (some z) epochDT.tz = false := by simp [sameTz, epochDT, tzUTC, hz0]
    unfold localTimezonePy
    simp [hz, dtSubPy, hs, dtSub_base self epochDT hv epochDT_valid, ho, epochDT_utcoffset env, offEq,
      bind, Except.bind, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]
  · refine ⟨?_, ?_⟩
    · simp [localTzFromTsPy, hf, hl, bind, Except.bind]
    · simp [localTzFromTsC, hl, bind, Except.bind]

end PyLean.Datetime
