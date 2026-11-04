import PyLean.Datetime.DateProps

/-!
`tzinfo` and `timezone`: the checks on `utcoffset()`, `dst()`, `tzname()`, the fixed
`timezone` methods and their twins. Properties are stated for every `TzEnv`, i.e. for
every `tzinfo` subclass, under the one type invariant `TzEnv.Valid`: what a method
returns as a `timedelta` is a valid `timedelta` object.
-/

namespace PyLean.Datetime

open PyLean

/-- A `timedelta` returned by a method is a real `timedelta` object. -/
def TzEnv.Valid (env : TzEnv) : Prop :=
  (∀ i a d, env.utcoffset i a = .ok (.delta d) → d.Valid) ∧
  (∀ i a d, env.dst i a = .ok (.delta d) → d.Valid)

/-- The invariant of a `tzinfo` object: a `timezone` holds a valid offset strictly
inside ±24h, and `timezone.utc` (`oid = 0`) is the zero offset with no name. -/
def Tz.Ok (tz : Tz) : Prop :=
  match tz.kind with
  | .timezone off name =>
    off.Valid ∧ -86400000000 < off.toUs ∧ off.toUs < 86400000000 ∧
      (tz.oid = 0 → off = ⟨0, 0, 0⟩ ∧ name = none)
  | .custom _ => True

def OptTzOk : Option Tz → Prop
  | none => True
  | some t => t.Ok

theorem check_twin (name : String) (r : OffRet) (h : ∀ d, r = .delta d → d.Valid) :
    checkUtcOffset name r = callTzinfoCheckC name r := by
  cases r with
  | none => rfl
  | other ty => rfl
  | delta o =>
    have hv := h o rfl
    unfold Delta.Valid MAX_DELTA_DAYS at hv
    simp only [checkUtcOffset, callTzinfoCheckC]
    unfold Delta.toUs
    by_cases hr : (o.days = -1 ∧ o.seconds = 0 ∧ o.us < 1) ∨ o.days < -1 ∨ o.days ≥ 1
    · rw [if_pos hr, if_pos (by omega)]
    · rw [if_neg hr, if_neg (by omega)]

theorem raw_off_valid (env : TzEnv) (henv : env.Valid) (tz : Tz) (htz : tz.Ok) (a : Option DT) (d : Delta) :
    tzUtcoffsetRaw env tz a = .ok (.delta d) → d.Valid := by
  unfold tzUtcoffsetRaw
  unfold Tz.Ok at htz
  split
  · rename_i off name hk
    rw [hk] at htz
    intro h
    cases h
    exact htz.1
  · exact henv.1 _ _ _

theorem raw_dst_valid (env : TzEnv) (henv : env.Valid) (tz : Tz) (a : Option DT) (d : Delta) :
    tzDstRaw env tz a = .ok (.delta d) → d.Valid := by
  unfold tzDstRaw
  split
  · intro h; cases h
  · exact henv.2 _ _ _

theorem off_twin (name : String) (r : Py OffRet)
    (hr : ∀ d, r = .ok (.delta d) → d.Valid) :
    (do checkUtcOffset name (← r)) = (do callTzinfoCheckC name (← r) : Py (Option Delta)) := by
  cases r with
  | error e => rfl
  | ok v =>
    show checkUtcOffset name v = callTzinfoCheckC name v
    apply check_twin
    intro d hd
    subst hd
    exact hr d rfl

theorem dt_utcoffset_twin (env : TzEnv) (henv : env.Valid) (dt : DT) (h : OptTzOk dt.tz) :
    dt.utcoffsetPy env = dt.utcoffsetC env := by
  unfold DT.utcoffsetPy DT.utcoffsetC
  split
  · rfl
  · rename_i tz htz
    rw [htz] at h
    exact off_twin _ _ (fun d hd => raw_off_valid env henv tz h _ d hd)

theorem dt_dst_twin (env : TzEnv) (henv : env.Valid) (dt : DT) :
    dt.dstPy env = dt.dstC env := by
  unfold DT.dstPy DT.dstC
  split
  · rfl
  · rename_i tz htz
    exact off_twin _ _ (fun d hd => raw_dst_valid env henv tz _ d hd)

theorem tm_utcoffset_twin (env : TzEnv) (henv : env.Valid) (t : TM) (h : OptTzOk t.tz) :
    t.utcoffsetPy env = t.utcoffsetC env := by
  unfold TM.utcoffsetPy TM.utcoffsetC
  split
  · rfl
  · rename_i tz htz
    rw [htz] at h
    exact off_twin _ _ (fun d hd => raw_off_valid env henv tz h _ d hd)

theorem tm_dst_twin (env : TzEnv) (henv : env.Valid) (t : TM) :
    t.dstPy env = t.dstC env := by
  unfold TM.dstPy TM.dstC
  split
  · rfl
  · rename_i tz htz
    exact off_twin _ _ (fun d hd => raw_dst_valid env henv tz _ d hd)

/-- A `utcoffset()` that passed the check lies strictly inside ±24h. -/
theorem checked_range (name : String) (r : OffRet) (o : Delta) (h : checkUtcOffset name r = .ok (some o)) :
    -86400000000 < o.toUs ∧ o.toUs < 86400000000 := by
  cases r with
  | none => cases h
  | other ty => cases h
  | delta d =>
    simp only [checkUtcOffset] at h
    split at h
    · cases h
    · cases h; omega

/-- `timezone.tzname()`/`str(tz)`: the two formatters agree on every valid
offset, including seconds and microseconds. -/
def TimezoneName : Prop :=
  ∀ (tz : Tz) (off : Delta) (name : Option String), tz.kind = .timezone off name → tz.Ok →
    timezoneStrPy off name = timezoneStrC tz.oid off name

theorem timezoneName_proven : TimezoneName := by
  intro tz off name hk hok
  unfold Tz.Ok at hok
  rw [hk] at hok
  obtain ⟨hv, h1, h2, hu⟩ := hok
  have hv' := hv
  unfold Delta.Valid MAX_DELTA_DAYS at hv'
  cases name with
  | some n => rfl
  | none =>
    simp only [timezoneStrPy, timezoneStrC, nameFromOffset]
    by_cases h0 : off.toUs = 0
    · have hz : off.days = 0 ∧ off.seconds = 0 ∧ off.us = 0 := by unfold Delta.toUs at h0; omega
      simp [h0, hz]
    · by_cases hoid : tz.oid = 0
      · have := (hu hoid).1
        subst this
        simp [Delta.toUs] at h0
      · have hz : ¬ (off.days = 0 ∧ off.seconds = 0 ∧ off.us = 0) := by
          intro hz; apply h0; unfold Delta.toUs; omega
        simp only [h0, hoid, hz, false_or, ite_false]
        by_cases hneg : off.days < 0
        · have ht : off.toUs < 0 := by unfold Delta.toUs; omega
          rw [newDeltaNormC_eq]
          have hin : -MAX_DELTA_DAYS ≤ ((-off.days * 86400 + -off.seconds) * 1000000 + -off.us) / 86400000000 ∧
              ((-off.days * 86400 + -off.seconds) * 1000000 + -off.us) / 86400000000 ≤ MAX_DELTA_DAYS := by
            unfold MAX_DELTA_DAYS Delta.toUs at *; omega
          simp only [mkDeltaN, hin, and_self, ite_true, hneg, ite_true, ht]
          generalize hT : (-off.days * 86400 + -off.seconds) * 1000000 + -off.us = T
          have hT' : off.toUs = -T := by unfold Delta.toUs; omega
          rw [hT'] at h1 h2 ht
          have ea : ((-T).natAbs : Int) = T := by omega
          have e1 : (((-T).natAbs / 3600000000 : Nat) : Int) = T / 1000000 % 86400 / 60 / 60 := by omega
          have e2 : (((-T).natAbs % 3600000000 / 60000000 : Nat) : Int) = T / 1000000 % 86400 / 60 % 60 := by omega
          have e3 : (((-T).natAbs % 3600000000 % 60000000 / 1000000 : Nat) : Int) = T / 1000000 % 86400 % 60 := by omega
          have e4 : (((-T).natAbs % 3600000000 % 60000000 % 1000000 : Nat) : Int) = T % 1000000 := by omega
          have c1 : ((-T).natAbs % 3600000000 % 60000000 % 1000000 = 0) ↔ (T % 1000000 = 0) := by omega
          have c2 : ((-T).natAbs % 3600000000 % 60000000 / 1000000 = 0) ↔ (T / 1000000 % 86400 % 60 = 0) := by omega
          simp only [hT']
          rw [e1, e2, e3, e4]
          simp only [ne_eq, c1, c2]
        · have ht : ¬ off.toUs < 0 := by unfold Delta.toUs; omega
          simp only [hneg, ite_false, ht]
          have ha : ((off.toUs.natAbs : Nat) : Int) = off.toUs := by omega
          generalize hT : off.toUs = T at *
          have hT2 : (off.days * 86400 + off.seconds) * 1000000 + off.us = T := hT
          have e1 : ((T.natAbs / 3600000000 : Nat) : Int) = off.seconds / 60 / 60 := by omega
          have e2 : ((T.natAbs % 3600000000 / 60000000 : Nat) : Int) = off.seconds / 60 % 60 := by omega
          have e3 : ((T.natAbs % 3600000000 % 60000000 / 1000000 : Nat) : Int) = off.seconds % 60 := by omega
          have e4 : ((T.natAbs % 3600000000 % 60000000 % 1000000 : Nat) : Int) = off.us := by omega
          have c1 : (T.natAbs % 3600000000 % 60000000 % 1000000 = 0) ↔ (off.us = 0) := by omega
          have c2 : (T.natAbs % 3600000000 % 60000000 / 1000000 = 0) ↔ (off.seconds % 60 = 0) := by omega
          rw [e1, e2, e3, e4]
          simp only [ne_eq, c1, c2]

/-- `tzinfo` base class: `tzname`, `utcoffset`, `dst` raise `NotImplementedError` in
both twins. -/
def TzinfoBase : Prop :=
  ∀ meth : String, (tzinfoBasePy meth).className = "NotImplementedError" ∧
    (tzinfoNogoC meth).className = "NotImplementedError"

theorem tzinfoBase_proven : TzinfoBase := fun _ => ⟨rfl, rfl⟩

/-- For `timezone` objects: `utcoffset` is the offset, `dst` is `None`, for any
argument the method accepts, in both twins; `__eq__` compares offsets only and equal
timezones hash alike. (`__getinitargs__` is `TimezoneGetinitargs`.) -/
def TimezoneMethods : Prop :=
  ∀ (env : TzEnv) (oid : Nat) (off off2 : Delta) (name name2 : Option String) (a : Option DT),
    off.Valid → off2.Valid →
    tzUtcoffsetRaw env ⟨oid, .timezone off name⟩ a = .ok (.delta off) ∧
    tzDstRaw env ⟨oid, .timezone off name⟩ a = .ok .none ∧
    some (timezoneEqPy off off2) = timezoneRichC .eq off off2 ∧
    timezoneRichC .lt off off2 = none ∧
    (timezoneEqPy off off2 = true → timezoneHashKey off = timezoneHashKey off2)

theorem timezoneMethods_proven : TimezoneMethods := by
  intro env oid off off2 name name2 a h1 h2
  refine ⟨rfl, rfl, ?_, by simp [timezoneRichC], ?_⟩
  · have := timedeltaCompare_proven off off2 .eq h1 h2
    simp only [timezoneRichC, timezoneEqPy, this.1, this.2]
    simp
  · intro h
    have e := (timedeltaCompare_proven off off2 .eq h1 h2).1
    rw [timezoneEqPy, e] at h
    simp only [CmpOp.holds, decide_eq_true_eq] at h
    exact (timedeltaBoolHash_proven off off2 h1 h2).2.1.mpr h

theorem createTimezoneC_fresh (oid : Nat) (off : Delta) (name : Option String)
    (h : off ≠ ⟨0, 0, 0⟩ ∨ name ≠ none) : createTimezoneC oid off name = ⟨oid, .timezone off name⟩ := by
  unfold createTimezoneC lookUpTimezoneC
  rw [if_neg (fun hh => by rcases h with h | h <;> exact h (by simp only [hh]))]

/-- `timezone(offset, name)`: the twins agree on the outcome for every valid offset (the
type invariant) and every name, and a zero offset without a name is the `timezone.utc`
singleton in both (in C `new_timezone`'s own test; `create_timezone`'s `look_up_timezone`
never fires on this path), while a zero offset with a name is a new object (`timezone(
timedelta(0), 'UTC') is not timezone.utc`), as is every nonzero in-range offset. -/
def TimezoneNew : Prop :=
  ∀ (oid : Nat) (off : Delta) (name : TzName), off.Valid →
    SameOutcome (timezoneNewPy oid off name) (timezoneNewC oid off name) ∧
    (off.toUs = 0 → timezoneNewPy oid off .omitted = .ok tzUTC ∧ timezoneNewC oid off .omitted = .ok tzUTC) ∧
    (∀ s, off.toUs = 0 → timezoneNewC oid off (.str s) = .ok ⟨oid, .timezone off (some s)⟩) ∧
    (-86400000000 < off.toUs → off.toUs < 86400000000 → off.toUs ≠ 0 →
      timezoneNewC oid off .omitted = .ok ⟨oid, .timezone off none⟩)

theorem timezoneNew_proven : TimezoneNew := by
  intro oid off name hv
  have hv' := hv
  unfold Delta.Valid MAX_DELTA_DAYS at hv'
  have hb : off.bool = true ↔ off.toUs ≠ 0 := (timedeltaBoolHash_proven off off hv hv).1
  have htw := (timezoneRange_proven off hv).2.2.2
  have hin : (off.days = -1 ∧ off.seconds = 0 ∧ off.us < 1) ∨ off.days < -1 ∨ off.days ≥ 1 ↔
      ¬(-86400000000 < off.toUs ∧ off.toUs < 86400000000) := by
    unfold Delta.toUs; omega
  have hz : off.toUs = 0 ↔ off = ⟨0, 0, 0⟩ := by
    constructor
    · intro e; unfold Delta.toUs at e
      obtain ⟨d, s, u⟩ := off
      simp only [Delta.mk.injEq]; simp only at hv' e; omega
    · intro e; rw [e]; rfl
  refine ⟨?_, fun h0 => ?_, fun s h0 => ?_, fun h1 h2 h0 => ?_⟩
  · cases name with
    | other => simp [timezoneNewPy, timezoneNewC, SameOutcome, PyExc.className]
    | omitted =>
      simp only [timezoneNewPy, timezoneNewC]
      by_cases h0 : off.bool = true
      · simp only [h0, Bool.not_true, Bool.false_eq_true, ite_false]
        rw [createTimezoneC_fresh oid off none (Or.inl (fun e => hb.mp h0 (hz.mpr e)))]
        revert htw
        cases timezonePy off <;> cases newTimezoneC off <;> simp [SameOutcome]
      · simp [h0, sameOutcome_refl]
    | str s =>
      simp only [timezoneNewPy, timezoneNewC]
      rw [createTimezoneC_fresh oid off (some s) (Or.inr (by simp))]
      unfold timezonePy
      by_cases h : (off.days = -1 ∧ off.seconds = 0 ∧ off.us < 1) ∨ off.days < -1 ∨ off.days ≥ 1
      · have hn := hin.mp h
        have h0 : off.toUs ≠ 0 := by intro e; apply hn; omega
        have h2 : ¬(-86399999999 ≤ off.toUs ∧ off.toUs ≤ 86399999999) := by intro e; apply hn; omega
        simp only [h0, h2, ite_false, h, ite_true]
        simp [SameOutcome, PyExc.className]
      · have hn : -86400000000 < off.toUs ∧ off.toUs < 86400000000 := by
          exact Classical.byContradiction (fun e => h (hin.mpr e))
        simp only [h, ite_false]
        by_cases h0 : off.toUs = 0
        · simp [h0, SameOutcome]
        · have h2 : -86399999999 ≤ off.toUs ∧ off.toUs ≤ 86399999999 := by omega
          simp [h0, h2, SameOutcome]
  · have : off.bool = false := by
      cases hc : off.bool
      · rfl
      · exact absurd h0 (hb.mp hc)
    exact ⟨by simp [timezoneNewPy, this], by simp [timezoneNewC, this]⟩
  · have e := hz.mp h0
    subst e
    simp [timezoneNewC, createTimezoneC_fresh]
  · have hbt : off.bool = true := hb.mpr h0
    have hr : ¬((off.days = -1 ∧ off.seconds = 0 ∧ off.us < 1) ∨ off.days < -1 ∨ off.days ≥ 1) :=
      fun e => hin.mp e ⟨h1, h2⟩
    simp only [timezoneNewC, hbt, Bool.not_true, Bool.false_eq_true, ite_false, newTimezoneC, h0, hr]
    rw [createTimezoneC_fresh oid off none (Or.inl (fun e => h0 (hz.mpr e)))]

end PyLean.Datetime
