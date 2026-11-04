import PyLean.Datetime.PickleProps
import PyLean.Datetime.OpenProps

/-!
`time._cmp` beyond the same-tzinfo case (review 50b4b958): equal offsets of different tzinfo
objects, naive against aware (`allow_mixed`'s 2 and the `TypeError`), and the whole-minute
offset arithmetic, each against C `time_richcompare`.
-/

namespace PyLean.Datetime
open PyLean

theorem cmp3 (a1 b1 c1 a2 b2 c2 : Int) (hb1 : 0 ≤ b1 ∧ b1 < 60) (hb2 : 0 ≤ b2 ∧ b2 < 60) :
    let d := if (a1 * 60 + b1) - (a2 * 60 + b2) = 0 then c1 - c2 else (a1 * 60 + b1) - (a2 * 60 + b2)
    (cmpTuple [a1, b1, c1] [a2, b2, c2] < 0 ↔ d < 0) ∧ (cmpTuple [a1, b1, c1] [a2, b2, c2] = 0 ↔ d = 0) := by
  intro d
  simp only [d]
  have e : cmpTuple [a1, b1, c1] [a2, b2, c2] = if a1 = a2 then (if b1 = b2 then (if c1 = c2 then 0
      else if c2 < c1 then 1 else -1) else if b2 < b1 then 1 else -1) else if a2 < a1 then 1 else -1 := by
    unfold cmpTuple
    by_cases h1 : a1 = a2 <;> by_cases h2 : b1 = b2 <;> by_cases h3 : c1 = c2 <;>
      simp [h1, h2, h3, tupleLt, eq_comm]
  rw [e]
  by_cases h1 : a1 = a2 <;> by_cases h2 : b1 = b2 <;> by_cases h3 : c1 = c2 <;>
    simp only [h1, h2, h3, ↓reduceIte] <;> (repeat' split) <;> first | omega | (simp <;> omega)

theorem tm_off_valid (env : TzEnv) (henv : env.Valid) (t : TM) (h : OptTzOk t.tz) (o : Delta)
    (ho : t.utcoffsetPy env = .ok (some o)) : o.Valid := by
  unfold TM.utcoffsetPy at ho
  split at ho
  · cases ho
  · rename_i tz htz
    rw [htz] at h
    cases hr : tzUtcoffsetRaw env tz none with
    | error e => rw [hr] at ho; cases ho
    | ok r =>
      rw [hr] at ho
      cases r with
      | none => simp [bind, Except.bind, checkUtcOffset] at ho
      | other ty => simp [bind, Except.bind, checkUtcOffset] at ho
      | delta d =>
        simp only [bind, Except.bind, checkUtcOffset] at ho
        split at ho
        · cases ho
        · cases ho; exact raw_off_valid env henv tz h none o hr

/-- `time` comparison for every pair of valid times whose tzinfos give whole-minute offsets
(every offset `timezone` and the common zones have): the twins agree for every operator,
through every branch of `time._cmp` (Py:1550-1576) and `time_richcompare` (:5027-5095): the
same tzinfo object, different objects with equal offsets (fields compared), naive against
aware (`==` false, `!=` true, ordering `TypeError` in both), and different offsets (the times
compared in UTC, Python by `(hh*60+mm - offset//1min, ss, us)`, C by seconds then
microseconds). An exception of either `utcoffset()` propagates in both. The sub-minute case is
the refuted `TimeCompareTwins`. -/
theorem timeCompareWholeMinutes_proven : TimeCompareWholeMinutes := by
  intro env op a b henv ha hb hwa hwb
  by_cases hs : sameTz a.tz b.tz = true
  · exact timeCompareBase_proven env op a b henv ha hb hs
  have hs' : sameTz a.tz b.tz = false := by simpa using hs
  have hm := time_memcmp a b ha hb
  have twa := tm_utcoffset_twin env henv a ha.2.2.2.2.2.2.2.2.2
  have twb := tm_utcoffset_twin env henv b hb.2.2.2.2.2.2.2.2.2
  cases hoa : a.utcoffsetPy env with
  | error e =>
    have hc : ∀ m, tmCmpPy env a b m = .error e := fun m => by
      simp [tmCmpPy, hs', hoa, bind, Except.bind]
    have hr : tmRichC env op a b = .error e := by
      rw [hoa] at twa; simp [tmRichC, hs', ← twa, bind, Except.bind]
    rw [hr]
    cases op <;> simp [tmRichPy, hc, bind, Except.bind, SameOutcome]
  | ok o1 =>
    cases hob : b.utcoffsetPy env with
    | error e =>
      have hc : ∀ m, tmCmpPy env a b m = .error e := fun m => by
        simp [tmCmpPy, hs', hoa, hob, bind, Except.bind]
      have hr : tmRichC env op a b = .error e := by
        rw [hoa] at twa; rw [hob] at twb; simp [tmRichC, hs', ← twa, ← twb, bind, Except.bind]
      rw [hr]
      cases op <;> simp [tmRichPy, hc, bind, Except.bind, SameOutcome]
    | ok o2 =>
      rw [hoa] at twa; rw [hob] at twb
      by_cases he : offEq o1 o2 = true
      · have hc : ∀ m, tmCmpPy env a b m = .ok (cmpTuple a.base b.base) := fun m => by
          simp [tmCmpPy, hs', hoa, hob, he, bind, Except.bind, pure, Except.pure]
        have hr : tmRichC env op a b = .ok (diffToBool (cmpTuple a.base b.base) op) := by
          simp [tmRichC, hs', ← twa, ← twb, he, hm, bind, Except.bind, pure, Except.pure]
        rw [hr]
        generalize cmpTuple a.base b.base = c at hc
        by_cases h0 : c = 0 <;>
          cases op <;> simp [tmRichPy, hc, h0, bind, Except.bind, pure, Except.pure, SameOutcome, diffToBool]
      · have he' : offEq o1 o2 = false := by simpa using he
        rcases o1 with _ | o1 <;> rcases o2 with _ | o2
        · simp [offEq] at he
        · -- naive against aware
          have hc : tmCmpPy env a b true = .ok 2 ∧ tmCmpPy env a b false = .error (.typeError "cannot compare naive and aware times") := by
            constructor <;> simp [tmCmpPy, hs', hoa, hob, he', bind, Except.bind, pure, Except.pure, throw,
              throwThe, MonadExcept.throw, MonadExceptOf.throw]
          cases op <;> simp [tmRichPy, tmRichC, hs', ← twa, ← twb, he', hc.1, hc.2, bind, Except.bind, pure,
            Except.pure, SameOutcome, PyExc.className, offEq, throw, throwThe, MonadExcept.throw,
            MonadExceptOf.throw]
        · have hc : tmCmpPy env a b true = .ok 2 ∧ tmCmpPy env a b false = .error (.typeError "cannot compare naive and aware times") := by
            constructor <;> simp [tmCmpPy, hs', hoa, hob, he', bind, Except.bind, pure, Except.pure, throw,
              throwThe, MonadExcept.throw, MonadExceptOf.throw]
          cases op <;> simp [tmRichPy, tmRichC, hs', ← twa, ← twb, he', hc.1, hc.2, bind, Except.bind, pure,
            Except.pure, SameOutcome, PyExc.className, offEq, throw, throwThe, MonadExcept.throw,
            MonadExceptOf.throw]
        · -- two different offsets, whole minutes
          have v1 := tm_off_valid env henv a ha.2.2.2.2.2.2.2.2.2 o1 hoa
          have v2 := tm_off_valid env henv b hb.2.2.2.2.2.2.2.2.2 o2 hob
          have w1 := hwa o1 hoa
          have w2 := hwb o2 hob
          obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, _⟩ := ha
          obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, _⟩ := hb
          unfold Delta.Valid at v1 v2
          unfold Delta.toUs at w1 w2
          have hu1 : o1.us = 0 := by omega
          have hu2 : o2.us = 0 := by omega
          have fm1 : floorMinutes o1 * 60 = o1.days * 86400 + o1.seconds := by
            unfold floorMinutes Delta.toUs; omega
          have fm2 : floorMinutes o2 * 60 = o2.days * 86400 + o2.seconds := by
            unfold floorMinutes Delta.toUs; omega
          have key := cmp3 (a.h * 60 + a.mi - floorMinutes o1) a.s a.us (b.h * 60 + b.mi - floorMinutes o2) b.s b.us
            ⟨a5, by omega⟩ ⟨b5, by omega⟩
          simp only at key
          have hc : ∀ m, tmCmpPy env a b m = .ok (cmpTuple [a.h * 60 + a.mi - floorMinutes o1, a.s, a.us]
              [b.h * 60 + b.mi - floorMinutes o2, b.s, b.us]) := fun m => by
            simp [tmCmpPy, hs', hoa, hob, he', bind, Except.bind, pure, Except.pure]
          obtain ⟨x, hx⟩ : ∃ x : Int, x = (if (a.h * 3600 + a.mi * 60 + a.s - o1.days * 86400 - o1.seconds) -
              (b.h * 3600 + b.mi * 60 + b.s - o2.days * 86400 - o2.seconds) = 0 then a.us - b.us
            else (a.h * 3600 + a.mi * 60 + a.s - o1.days * 86400 - o1.seconds) -
              (b.h * 3600 + b.mi * 60 + b.s - o2.days * 86400 - o2.seconds)) := ⟨_, rfl⟩
          have hr : tmRichC env op a b = .ok (diffToBool x op) := by
            rw [hx]; simp [tmRichC, hs', ← twa, ← twb, he', bind, Except.bind, pure, Except.pure]
          have eqd : (a.h * 3600 + a.mi * 60 + a.s - o1.days * 86400 - o1.seconds) -
              (b.h * 3600 + b.mi * 60 + b.s - o2.days * 86400 - o2.seconds) =
              ((a.h * 60 + a.mi - floorMinutes o1) * 60 + a.s) - ((b.h * 60 + b.mi - floorMinutes o2) * 60 + b.s) := by
            omega
          rw [eqd] at hx
          have hk1 : cmpTuple [a.h * 60 + a.mi - floorMinutes o1, a.s, a.us]
              [b.h * 60 + b.mi - floorMinutes o2, b.s, b.us] < 0 ↔ x < 0 := by
            rw [key.1, hx]
          have hk2 : cmpTuple [a.h * 60 + a.mi - floorMinutes o1, a.s, a.us]
              [b.h * 60 + b.mi - floorMinutes o2, b.s, b.us] = 0 ↔ x = 0 := by
            rw [key.2, hx]
          rw [hr]
          generalize cmpTuple [a.h * 60 + a.mi - floorMinutes o1, a.s, a.us]
              [b.h * 60 + b.mi - floorMinutes o2, b.s, b.us] = c at hc hk1 hk2
          have k1 := hk1.mp; have k2 := hk1.mpr; have k3 := hk2.mp; have k4 := hk2.mpr
          by_cases h0 : c = 0
          · have hx0 : x = 0 := k3 h0
            subst h0; subst hx0
            cases op <;> simp [tmRichPy, hc, bind, Except.bind, pure, Except.pure, SameOutcome, diffToBool]
          · have hx0 : x ≠ 0 := fun e => h0 (k4 e)
            by_cases hn : c < 0
            · have hxn : x < 0 := k1 hn
              cases op <;> simp [tmRichPy, hc, bind, Except.bind, pure, Except.pure, SameOutcome, diffToBool,
                h0, hx0] <;> omega
            · have hxn : ¬ x < 0 := fun e => hn (k2 e)
              cases op <;> simp [tmRichPy, hc, bind, Except.bind, pure, Except.pure, SameOutcome, diffToBool,
                h0, hx0] <;> omega

end PyLean.Datetime
