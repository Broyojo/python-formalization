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

/-! ### `astimezone` -/

theorem dtFromTotal_totalUs (T : Int) (tz : Option Tz) (h1 : 1 ≤ T / 86400000000) (h2 : T / 86400000000 ≤ MAXORDINAL) :
    (dtFromTotal T tz).totalUs = T := by
  obtain ⟨-, ho, -⟩ := ord2ymd_valid (T / 86400000000) h1 h2
  unfold dtFromTotal DT.totalUs
  simp only [ho]
  omega

/-- A zone built from `localtime` is a `timezone` with the new identity, a valid offset strictly
inside a day and a name. -/
theorem localTzFromTsPy_shape (ltz : Int → Py LocalTmZ) (oid : Nat) (ts : Int) (z : Tz) (h0 : oid ≠ 0)
    (h : localTzFromTsPy ltz oid ts = .ok z) :
    z.oid = oid ∧ ∃ d s, z.kind = .timezone d (some s) ∧ z.Ok := by
  unfold localTzFromTsPy at h
  by_cases hf : fitsTimeT ts
  · simp only [hf, not_true_eq_false, ↓reduceIte, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i r _
      obtain ⟨_, g, zn⟩ := r
      simp only at h
      split at h
      · cases h
      · rename_i d hd
        have dv := ((mkDeltaPy_spec _).1 d (by rw [← deltaPy_eq]; exact hd)).1
        simp only [timezoneNewPy] at h
        cases hz : timezonePy d with
        | error e => rw [hz] at h; cases h
        | ok _ =>
          rw [hz] at h
          cases h
          refine ⟨rfl, d, zn, rfl, ?_⟩
          unfold Tz.Ok
          have hr : -86399999999 ≤ d.toUs ∧ d.toUs ≤ 86399999999 := by
            unfold timezonePy at hz
            split at hz
            · omega
            · split at hz
              · omega
              · cases hz
          exact ⟨dv, by omega, by omega, fun e => absurd e h0⟩
  · simp [hf, bind, Except.bind, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at h

/-- The end of `astimezone` to a `timezone` `tz`: `(self - o).replace(tzinfo=tz)` and
`tz.fromutc` (Py:2157-2160) against `self - offset` with `tz` attached and `fromutc`
(:6957-7002), for every valid `self` and valid offset `o`. -/
theorem astz_tail (env : TzEnv) (self : DT) (o : Delta) (tz : Tz) (off : Delta) (name : Option String)
    (hv : self.Valid) (ov : o.Valid) (htz : tz.Ok) (hk : tz.kind = .timezone off name) :
    SameOutcome
      (do let u ← dtSubDeltaPy self o
          let u ← dtReplace u none none none none none none none none (some (some tz))
          tzFromutcPy env tz u)
      (do let r ← addDatetimeTimedeltaC self o (-1)
          tzFromutcC env tz { r with tz := some tz }) := by
  have offv : off.Valid := by have := htz; unfold Tz.Ok at this; rw [hk] at this; exact this.1
  have hs := datetimeSubTimedelta_proven self o hv ov
  simp only at hs
  by_cases hr : 1 ≤ (self.totalUs - o.toUs) / 86400000000 ∧ (self.totalUs - o.toUs) / 86400000000 ≤ MAXORDINAL
  · obtain ⟨hp, hc⟩ := hs.1 hr
    rw [hp, hc]
    have hu : (dtFromTotal (self.totalUs - o.toUs) (some tz)).Valid := dtFromTotal_valid _ _ hr.1 hr.2 htz
    have hrep : dtReplace (dtFromTotal (self.totalUs - o.toUs) self.tz) none none none none none none none none
        (some (some tz)) = .ok (dtFromTotal (self.totalUs - o.toUs) (some tz)) := by
      unfold dtReplace
      exact newDT_ok _ hu
    have hrc : ({ dtFromTotal (self.totalUs - o.toUs) self.tz with tz := some tz } : DT) =
        dtFromTotal (self.totalUs - o.toUs) (some tz) := rfl
    simp only [bind, Except.bind, hrep, hrc]
    simp only [tzFromutcPy, tzFromutcC, hk, timezoneFromutcPy, timezoneFromutcC]
    have htzeq : (dtFromTotal (self.totalUs - o.toUs) (some tz)).tz = some tz := rfl
    simp only [htzeq, Option.map_some, ne_eq, not_true_eq_false, ↓reduceIte]
    have ha := datetimeAddTimedelta_proven (dtFromTotal (self.totalUs - o.toUs) (some tz)) off hu offv
    simp only at ha
    by_cases hr2 : 1 ≤ ((dtFromTotal (self.totalUs - o.toUs) (some tz)).totalUs + off.toUs) / 86400000000 ∧
        ((dtFromTotal (self.totalUs - o.toUs) (some tz)).totalUs + off.toUs) / 86400000000 ≤ MAXORDINAL
    · obtain ⟨p2, c2⟩ := ha.1 hr2
      rw [p2, c2]; simp [SameOutcome]
    · obtain ⟨p2, c2⟩ := ha.2 hr2
      obtain ⟨e1, q1, k1⟩ := p2
      obtain ⟨e2, q2, k2⟩ := c2
      rw [q1, q2]; simp [SameOutcome, k1, k2]
  · obtain ⟨p, c⟩ := hs.2 hr
    obtain ⟨e1, q1, k1⟩ := p
    obtain ⟨e2, q2, k2⟩ := c
    rw [q1, q2]; simp [bind, Except.bind, SameOutcome, k1, k2]

theorem tz_raw_timezone (env : TzEnv) (z : Tz) (d : Delta) (s : Option String) (a : Option DT)
    (hk : z.kind = .timezone d s) : tzUtcoffsetRaw env z a = .ok (.delta d) := by
  unfold tzUtcoffsetRaw; rw [hk]

theorem check_in_range (d : Delta) (hv : d.Valid) (h1 : -86400000000 < d.toUs) (h2 : d.toUs < 86400000000) :
    callTzinfoCheckC "utcoffset" (.delta d) = .ok (some d) := by
  simp only [callTzinfoCheckC]
  unfold Delta.Valid MAX_DELTA_DAYS at hv
  unfold Delta.toUs at h1 h2
  rw [if_neg (by omega)]

theorem raw_of_utcoffset (env : TzEnv) (self : DT) (z : Tz) (hz : self.tz = some z) (r : Option Delta)
    (h : self.utcoffsetPy env = .ok r) :
    (r = none → tzUtcoffsetRaw env z (some self) = .ok .none) ∧
    (∀ o, r = some o → tzUtcoffsetRaw env z (some self) = .ok (.delta o) ∧
      -86400000000 < o.toUs ∧ o.toUs < 86400000000) := by
  unfold DT.utcoffsetPy at h
  rw [hz] at h
  simp only [bind, Except.bind] at h
  cases hr : tzUtcoffsetRaw env z (some self) with
  | error e => rw [hr] at h; cases h
  | ok v =>
    rw [hr] at h
    cases v with
    | none => simp only [checkUtcOffset, Except.ok.injEq] at h; subst h; simp
    | other ty => simp [checkUtcOffset] at h
    | delta d =>
      simp only [checkUtcOffset] at h
      split at h
      · cases h
      · cases h
        rename_i hrange
        refine ⟨fun e => absurd e (by simp), fun o e => ?_⟩
        rw [Option.some.injEq] at e
        subst e
        exact ⟨rfl, by omega, by omega⟩

/-- `local_timezone` of the UTC datetime `self - offset` (:6987-6993): the zone of
`floor((T - epoch) / 1 s)`. -/
theorem localTimezoneC_utc (env : TzEnv) (ltz : Int → Py LocalTmZ) (oid : Nat) (T : Int)
    (h1 : 1 ≤ T / 86400000000) (h2 : T / 86400000000 ≤ MAXORDINAL) :
    localTimezoneC env ltz oid (dtFromTotal T (some tzUTC)) =
      localTzFromTsC ltz oid ((T - epochC * 1000000) / 1000000) := by
  have hv : (dtFromTotal T (some tzUTC)).Valid := dtFromTotal_valid T _ h1 h2 epochDT_valid.2.2.2.2.2.2.2.2.2.2
  have hb := dtSub_baseC _ _ hv epochDT_valid
  rw [dtFromTotal_totalUs T _ h1 h2, epochDT_totalUs] at hb
  have hs : sameTz (dtFromTotal T (some tzUTC)).tz epochDT.tz = true := by
    simp [sameTz, dtFromTotal, epochDT]
  have hf : fitsTimeT ((T - epochC * 1000000) / 1000000) := by
    unfold fitsTimeT epochC; unfold MAXORDINAL at h2; omega
  unfold localTimezoneC dtSubC
  simp only [hs, ↓reduceIte, bind, Except.bind, pure, Except.pure, hb, canon_toUs, hf, not_true_eq_false]

/-- `datetime.astimezone` with the local zone (Py:2137-2160 against
`datetime_datetime_astimezone_impl`, :6914-7004), for every valid datetime, tzinfo environment
and C-library `localtime` with fields a `datetime` accepts, the new zones having fresh
identities (`o1` for the target zone, `o2` for `self`'s; neither is 0 nor the identity of a
tzinfo in play, and identity 0 is `timezone.utc` itself): (a) to a `timezone` from a naive
datetime, or from one whose tzinfo answers `utcoffset() is None` (that tzinfo not being the
target, the case `datetime-pydatetime-astimezone-unchecked-offset` records), both twins take
`self`'s local zone (`_local_timezone`, `local_timezone_from_local`) and give the same datetime
or the same exception class; (b) to the local zone (`tz=None`) from an aware datetime with an
offset, when `self - offset` stays in range, both build the zone of the same UTC timestamp and
agree; (c) a non-tzinfo argument is `TypeError` in both. -/
def AstimezoneLocal : Prop :=
  ∀ (env : TzEnv) (ltz : Int → Py LocalTmZ) (o1 o2 : Nat) (self : DT),
    env.Valid → self.Valid → (∀ v r, ltz v = .ok r → LocalTmValid r.1) →
    o1 ≠ 0 → o2 ≠ 0 → (∀ z, self.tz = some z → z.oid ≠ o1 ∧ (z.oid = 0 → z = tzUTC)) →
    (∀ t off name, t.Ok → t.kind = .timezone off name → t.oid ≠ o2 → (∀ z, self.tz = some z → z.oid ≠ t.oid) →
      (self.tz = none ∨ self.utcoffsetPy env = .ok none) →
      SameOutcome (dtAstimezoneFullPy env ltz o1 o2 self (.tz t)) (dtAstimezoneFullC env ltz o1 o2 self (.tz t))) ∧
    (∀ o, self.tz ≠ none → self.utcoffsetPy env = .ok (some o) →
      1 ≤ (self.totalUs - o.toUs) / 86400000000 → (self.totalUs - o.toUs) / 86400000000 ≤ MAXORDINAL →
      SameOutcome (dtAstimezoneFullPy env ltz o1 o2 self .none_) (dtAstimezoneFullC env ltz o1 o2 self .none_)) ∧
    ((dtAstimezoneFullPy env ltz o1 o2 self .other).raises "TypeError" ∧
      (dtAstimezoneFullC env ltz o1 o2 self .other).raises "TypeError")

@[simp] theorem py_ok_bind {α β : Type} (x : α) (f : α → Py β) : ((Except.ok x : Py α) >>= f) = f x := rfl

/-- The ends of both twins with offset `o` of a `mytz` that is not the `timezone` target `t`. -/
theorem astz_tail_twin (env : TzEnv) (ltz : Int → Py LocalTmZ) (o1 : Nat) (self : DT) (t mytz : Tz) (o : Delta)
    (off : Delta) (name : Option String) (hv : self.Valid) (ov : o.Valid) (htok : t.Ok)
    (hk : t.kind = .timezone off name) (hne : ¬ t.oid = mytz.oid) :
    SameOutcome (astzPyTail env self t mytz (.delta o)) (astzCFinish env ltz o1 self (some t) o) := by
  unfold astzPyTail astzCFinish
  simp only [hne, ↓reduceIte, pure_bind]
  exact astz_tail env self o t off name hv ov htok hk

/-- Both twins once `self`'s local zone is known (`pz` in Python, `cz` in C), for a `timezone`
target `t`. -/
theorem astz_local_self (env : TzEnv) (ltz : Int → Py LocalTmZ) (o1 : Nat) (self : DT) (t : Tz) (off : Delta)
    (name : Option String) (o2 : Nat)
    (hv : self.Valid) (htok : t.Ok) (hk : t.kind = .timezone off name) (ht2 : t.oid ≠ o2)
    (pz cz : Py Tz) (hs : SameOutcome pz cz)
    (hshape : ∀ z, pz = .ok z → z.oid = o2 ∧ ∃ d s, z.kind = .timezone d (some s) ∧ z.Ok) :
    SameOutcome
      (pz >>= fun z => tzUtcoffsetRaw env z (some self) >>= fun mo => astzPyTail env self t z mo)
      (cz >>= fun z => astzCAfterLocal env ltz o1 self (some t) z) := by
  cases pz with
  | error e1 =>
    cases cz with
    | error e2 => simpa [bind, Except.bind, SameOutcome] using hs
    | ok _ => cases hs
  | ok z =>
    cases cz with
    | error _ => cases hs
    | ok z' =>
      simp only [SameOutcome] at hs
      subst hs
      obtain ⟨hzo, d, s, hzk, hzok⟩ := hshape z rfl
      have hraw := tz_raw_timezone env z d (some s) (some self) hzk
      have dok : d.Valid ∧ -86400000000 < d.toUs ∧ d.toUs < 86400000000 := by
        have := hzok; unfold Tz.Ok at this; rw [hzk] at this; exact ⟨this.1, this.2.1, this.2.2.1⟩
      have hne : ¬ t.oid = z.oid := by rw [hzo]; exact ht2
      have hne' : ¬ Option.map (fun x : Tz => x.oid) (some t) = some z.oid := by simp [hne]
      show SameOutcome (tzUtcoffsetRaw env z (some self) >>= fun mo => astzPyTail env self t z mo)
        (astzCAfterLocal env ltz o1 self (some t) z)
      unfold astzCAfterLocal
      simp only [hraw, hne', ↓reduceIte, check_in_range d dok.1 dok.2.1 dok.2.2, py_ok_bind]
      exact astz_tail_twin env ltz o1 self t z d off name hv dok.1 htok hk hne

theorem localTimezonePy_naive_shape (env : TzEnv) (ltz : Int → Py LocalTmZ) (oid : Nat) (self : DT) (h0 : oid ≠ 0)
    (hn : self.tz = none) (z : Tz) (hz : localTimezonePy env ltz oid self = .ok z) :
    z.oid = oid ∧ ∃ d s, z.kind = .timezone d (some s) ∧ z.Ok := by
  unfold localTimezonePy at hz
  simp only [hn, Option.isNone_none, ↓reduceIte, bind, Except.bind] at hz
  split at hz
  · cases hz
  · exact localTzFromTsPy_shape ltz oid _ z h0 hz

theorem astimezoneLocal_proven : AstimezoneLocal := by
  intro env ltz o1 o2 self henv hv hlt h1 h2 hself
  refine ⟨fun t off name htok hk ht2 htz hcase => ?_, fun o hn ho hr1 hr2 => ?_, ?_⟩
  · -- (a): the local zone of the fields of `self`
    have hself' : ({ self with tz := none } : DT).Valid := by
      obtain ⟨a, b, c, d, e, f, g, i, j, k, _⟩ := hv; exact ⟨a, b, c, d, e, f, g, i, j, k, trivial⟩
    have hnoutc : ∀ z, ({ self with tz := none } : DT).tz = some z → z.oid = 0 → z = tzUTC := by
      intro z hz; cases hz
    have ha := (localTimezoneFull_proven env ltz o2 { self with tz := none } henv hself' hlt hnoutc).1 rfl
    have hloc : localTimezoneFromLocalC ltz o2 { self with tz := none } = localTimezoneFromLocalC ltz o2 self := rfl
    rw [hloc] at ha
    have hshape := localTimezonePy_naive_shape env ltz o2 { self with tz := none } h2 rfl
    by_cases hn : self.tz = none
    · have hs0 : ({ self with tz := none } : DT) = self := by cases self; simp_all
      rw [hs0] at ha hshape
      unfold dtAstimezoneFullPy dtAstimezoneFullC
      simp only [hn, pure_bind]
      exact astz_local_self env ltz o1 self t off name o2 hv htok hk ht2 _ _ ha hshape
    · have hnone : self.utcoffsetPy env = .ok none := hcase.resolve_left hn
      cases hz : self.tz with
      | none => exact absurd hz hn
      | some z =>
        have hraw := (raw_of_utcoffset env self z hz none hnone).1 rfl
        have hrep : dtReplace self none none none none none none none none (some none) = .ok { self with tz := none } := by
          unfold dtReplace; exact newDT_ok _ hself'
        have hne : ¬ Option.map (fun x : Tz => x.oid) (some t) = some z.oid := by
          have := htz z hz; simp only [Option.map_some, Option.some.injEq]; omega
        have hchk : callTzinfoCheckC "utcoffset" .none = .ok none := rfl
        unfold dtAstimezoneFullPy dtAstimezoneFullC
        simp only [hz, hraw, hrep, hne, hchk, ↓reduceIte, pure_bind, py_ok_bind]
        exact astz_local_self env ltz o1 self t off name o2 hv htok hk ht2 _ _ ha hshape
  · -- (b): to the local zone from an aware datetime
    obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.mp hn
    obtain ⟨hz1, hutc⟩ := hself z hz
    obtain ⟨hraw, hlo, hhi⟩ := (raw_of_utcoffset env self z hz (some o) ho).2 o rfl
    have hutc' : ∀ w, self.tz = some w → w.oid = 0 → w = tzUTC := by
      intro w hw; rw [hz] at hw; cases hw; exact hutc
    have hP := (localTimezoneFull_proven env ltz o1 self henv hv hlt hutc').2.1 o hn ho
    have ov : o.Valid := dt_offset_valid env henv self hv.2.2.2.2.2.2.2.2.2.2 o ho
    have hchk := check_in_range o ov hlo hhi
    have hsub := (datetimeSubTimedelta_proven self o hv ov).1 ⟨hr1, hr2⟩
    have hC := localTimezoneC_utc env ltz o1 (self.totalUs - o.toUs) hr1 hr2
    have hf : fitsTimeT ((self.totalUs - o.toUs - epochC * 1000000) / 1000000) := by
      unfold fitsTimeT epochC; unfold MAXORDINAL at hr2; omega
    have htw := localTzFromTs_twin ltz o1 _ hf
    have hn0 : ¬ Option.map (fun x : Tz => x.oid) (none : Option Tz) = some z.oid := by simp
    -- C: the offset, `self - offset` and the zone of the UTC result
    have hCfin : astzCFinish env ltz o1 self none o =
        (localTzFromTsC ltz o1 ((self.totalUs - o.toUs - epochC * 1000000) / 1000000) >>= fun w =>
          tzFromutcC env w { dtFromTotal (self.totalUs - o.toUs) self.tz with tz := some w }) := by
      unfold astzCFinish
      simp only [hsub.2, bind, Except.bind]
      have hrc : ({ dtFromTotal (self.totalUs - o.toUs) self.tz with tz := some tzUTC } : DT) =
          dtFromTotal (self.totalUs - o.toUs) (some tzUTC) := rfl
      rw [hrc, hC]
    unfold dtAstimezoneFullPy dtAstimezoneFullC
    simp only [hz, hraw, hP, hn0, hchk, ↓reduceIte, pure_bind, py_ok_bind, hCfin]
    cases hp : localTzFromTsPy ltz o1 ((self.totalUs - o.toUs - epochC * 1000000) / 1000000) with
    | error e1 =>
      rw [hp] at htw
      cases hc : localTzFromTsC ltz o1 ((self.totalUs - o.toUs - epochC * 1000000) / 1000000) with
      | error e2 => rw [hc] at htw; simpa [bind, Except.bind, SameOutcome] using htw
      | ok _ => rw [hc] at htw; cases htw
    | ok w =>
      rw [hp] at htw
      cases hc : localTzFromTsC ltz o1 ((self.totalUs - o.toUs - epochC * 1000000) / 1000000) with
      | error _ => rw [hc] at htw; cases htw
      | ok w' =>
        rw [hc] at htw
        simp only [SameOutcome] at htw
        subst htw
        obtain ⟨hwo, d, s, hwk, hwok⟩ := localTzFromTsPy_shape ltz o1 _ w h1 hp
        have hne : ¬ w.oid = z.oid := by rw [hwo]; exact fun e => hz1 e.symm
        have := astz_tail_twin env ltz o1 self w z o d (some s) hv ov hwok hwk hne
        unfold astzCFinish at this
        simp only [hsub.2, pure_bind, py_ok_bind] at this
        show SameOutcome (astzPyTail env self w z (.delta o)) _
        exact this
  · refine ⟨⟨.typeError "tz argument must be an instance of tzinfo", ?_, rfl⟩,
      ⟨.typeError "~tzinfo argument must be None or of a tzinfo subclass", ?_, rfl⟩⟩
    · simp [dtAstimezoneFullPy, bind, Except.bind, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]
    · simp [dtAstimezoneFullC, bind, Except.bind, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]

/-! ### Where the twins part: the target zone of `astimezone()` -/

instance sameOutcomeDecidable {α : Type} [DecidableEq α] (x y : Py α) : Decidable (SameOutcome x y) := by
  cases x <;> cases y <;> simp only [SameOutcome] <;> infer_instance

/-- A zone that springs forward by an hour at the epoch: UTC before it (`STD`), UTC+1 from
it on (`DST`), so the local times 00:00-00:59 of 1970-01-01 do not exist. -/
def gapZone (u : Int) : Py LocalTmZ := do
  let off : Int := if u < 0 then 0 else 3600
  let s := u + off
  let o := ord2ymd (s / 86400 + 719163)
  let ymd ← checkDate o.1 o.2.1 o.2.2
  let r := s % 86400
  return ((ymd.1, ymd.2.1, ymd.2.2, r / 3600, r % 3600 / 60, r % 60), off, if u < 0 then "STD" else "DST")

theorem checkDate_valid (y m d : Int) (v : Int × Int × Int) (h : checkDate y m d = .ok v) :
    ValidDate y m d ∧ v = (y, m, d) := by
  by_cases hv : ValidDate y m d
  · rw [checkDate_ok _ _ _ hv] at h; cases h; exact ⟨hv, rfl⟩
  · obtain ⟨e, he, _⟩ := checkDate_err y m d hv
    rw [he] at h; cases h

theorem gapZone_valid : ∀ v r, gapZone v = .ok r → LocalTmValid r.1 := by
  intro v r h
  unfold gapZone at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i ymd hy
    cases h
    obtain ⟨hd, rfl⟩ := checkDate_valid _ _ _ _ hy
    unfold LocalTmValid
    refine ⟨hd, ?_⟩
    dsimp only
    generalize (v + if v < 0 then 0 else 3600) = s
    omega

/-- `astimezone()` (`tz=None`) on a naive datetime agrees between the twins for every valid
datetime and every C-library `localtime` with fields a `datetime` accepts. -/
def AstimezoneLocalNaiveTwins : Prop :=
  ∀ (env : TzEnv) (ltz : Int → Py LocalTmZ) (o1 o2 : Nat) (self : DT),
    env.Valid → self.Valid → self.tz = none → (∀ v r, ltz v = .ok r → LocalTmValid r.1) →
    o1 ≠ 0 → o2 ≠ 0 → o1 ≠ o2 →
    SameOutcome (dtAstimezoneFullPy env ltz o1 o2 self .none_) (dtAstimezoneFullC env ltz o1 o2 self .none_)

/-- `datetime(1970, 1, 1, 0, 30).astimezone()` in `gapZone`, a wall time in the gap: Python
takes the target zone from `self._local_timezone()` of the naive wall time (UTC+0 for fold 0)
and returns `00:30` with that zone; C converts to UTC first and takes the zone of the UTC
result (`local_timezone(result)`, UTC+1) and returns `01:30+01:00`. The same instant, a
different wall time and tzinfo (the bug record reproduces it with `TZ=EST5EDT`). -/
theorem astimezoneLocalNaiveTwins_refuted : ¬ AstimezoneLocalNaiveTwins := by
  intro h
  have hv : (⟨1970, 1, 1, 0, 30, 0, 0, 0, none⟩ : DT).Valid := by
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      Or.inl rfl, trivial⟩
  have := h emptyEnv gapZone 7 8 ⟨1970, 1, 1, 0, 30, 0, 0, 0, none⟩ emptyEnv_valid hv rfl gapZone_valid
    (by decide) (by decide) (by decide)
  revert this
  decide +kernel

/-- A `localtime` that always reports 2020-01-02 03:00:00 UTC (enough to run both twins). -/
def constZone (_ : Int) : Py LocalTmZ := .ok ((2020, 1, 2, 3, 0, 0), 0, "UTC")

theorem constZone_valid : ∀ v r, constZone v = .ok r → LocalTmValid r.1 := by
  intro v r h
  cases h
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- `astimezone()` (`tz=None`) on an aware datetime whose tzinfo's `utcoffset()` is `None`
agrees between the twins. -/
def AstimezoneLocalNoneOffsetTwins : Prop :=
  ∀ (env : TzEnv) (ltz : Int → Py LocalTmZ) (o1 o2 : Nat) (self : DT),
    env.Valid → self.Valid → self.tz ≠ none → self.utcoffsetPy env = .ok none →
    (∀ v r, ltz v = .ok r → LocalTmValid r.1) → o1 ≠ 0 → o2 ≠ 0 → o1 ≠ o2 →
    (∀ z, self.tz = some z → z.oid ≠ o1 ∧ z.oid ≠ o2 ∧ z.oid ≠ 0) →
    SameOutcome (dtAstimezoneFullPy env ltz o1 o2 self .none_) (dtAstimezoneFullC env ltz o1 o2 self .none_)

/-- `datetime(2020, 1, 2, 3, tzinfo=T()).astimezone()` with `T.utcoffset` returning `None`:
Python computes the target zone first, `self._local_timezone()`, whose aware branch
`self - _EPOCH` raises `TypeError('cannot mix naive and timezone-aware time')`; C treats `self`
as naive (`goto naive`) and converts. -/
theorem astimezoneLocalNoneOffsetTwins_refuted : ¬ AstimezoneLocalNoneOffsetTwins := by
  intro h
  have hv : (⟨2020, 1, 2, 3, 0, 0, 0, 0, some ⟨5, .custom 0⟩⟩ : DT).Valid := by
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      Or.inl rfl, trivial⟩
  have := h emptyEnv constZone 7 8 ⟨2020, 1, 2, 3, 0, 0, 0, 0, some ⟨5, .custom 0⟩⟩ emptyEnv_valid hv
    (by simp) rfl constZone_valid (by decide) (by decide) (by decide)
    (fun z hz => by cases hz; decide)
  revert this
  decide +kernel

end PyLean.Datetime

