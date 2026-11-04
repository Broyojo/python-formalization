import PyLean.Datetime.ChangedProps

/-!
`_parse_isoformat_time` (Lib/_pydatetime.py:453-519) on every shape of its argument: a time
part with no offset, with a trailing `Z`, with a `+`/`-` offset of any form, and the
refusals, for any time part and offset text, with `_parse_hh_mm_ss_ff` (pinned on its own by
`ParseHHMMSSFFForms` and `ParseHHMMSSFFFraction`) abstracted to its result.
-/

namespace PyLean.Datetime
open PyLean

/-- No time-zone designator (`-`, `+`, `Z`) in `s`. -/
def NoDesig (s : List Char) : Prop := ∀ x ∈ s, x ≠ '-' ∧ x ≠ '+' ∧ x ≠ 'Z'

theorem findPlusOne_none (s : List Char) (c : Char) (h : ∀ x ∈ s, x ≠ c) : findPlusOne s c = 0 := by
  unfold findPlusOne
  rw [List.findIdx?_eq_none_iff.mpr (by intro x hx; simpa using h x hx)]

theorem findPlusOne_at (t r : List Char) (c : Char) (h : ∀ x ∈ t, x ≠ c) :
    findPlusOne (t ++ c :: r) c = t.length + 1 := by
  induction t with
  | nil => simp [findPlusOne, List.findIdx?_cons]
  | cons x t ih =>
    have hx : x ≠ c := h x (by simp)
    have ih' := ih (fun y hy => h y (by simp [hy]))
    unfold findPlusOne at ih' ⊢
    cases e : List.findIdx? (· = c) (t ++ c :: r) with
    | none => rw [e] at ih'; simp at ih'
    | some i =>
      rw [e] at ih'
      simp only [List.cons_append, List.findIdx?_cons, hx, decide_false, Bool.false_eq_true, ↓reduceIte, e,
        Option.map_some, List.length_cons]
      simp at ih'; omega

theorem tz_pre (t : List Char) (ha : isAsciiStr t = true) (hl : 2 ≤ t.length) (hd : NoDesig t)
    (H M S U : Int) (hp : parseHHMMSSFFPy t = .ok (H, M, S, U)) (hH : H ≠ 24) :
    parseIsoTimePy t = .ok (⟨H, M, S, U, none⟩, false, false, none) := by
  have f1 := findPlusOne_none t '-' (fun x hx => (hd x hx).1)
  have f2 := findPlusOne_none t '+' (fun x hx => (hd x hx).2.1)
  have f3 := findPlusOne_none t 'Z' (fun x hx => (hd x hx).2.2)
  unfold parseIsoTimePy
  simp [show ¬ t.length < 2 by omega, ha, f1, f2, f3, hp, hH, bind, Except.bind, pure, Except.pure]
  intro h; omega

theorem tz_Z (t : List Char) (ha : isAsciiStr t = true) (hl : 2 ≤ t.length) (hd : NoDesig t)
    (H M S U : Int) (hp : parseHHMMSSFFPy t = .ok (H, M, S, U)) (hH : H ≠ 24) :
    parseIsoTimePy (t ++ ['Z']) = .ok (⟨H, M, S, U, some 0⟩, false, false, none) := by
  have f1 := findPlusOne_none (t ++ ['Z']) '-' (fun x hx => by
    simp at hx; rcases hx with hx | hx; exact (hd x hx).1; subst hx; decide)
  have f2 := findPlusOne_none (t ++ ['Z']) '+' (fun x hx => by
    simp at hx; rcases hx with hx | hx; exact (hd x hx).2.1; subst hx; decide)
  have f3 := findPlusOne_at t [] 'Z' (fun x hx => (hd x hx).2.2)
  have ha' : isAsciiStr (t ++ ['Z']) = true := by
    unfold isAsciiStr at *; simp at ha ⊢; exact ha
  unfold parseIsoTimePy
  simp [show ¬ t.length + 1 < 2 by omega, ha', f1, f2, f3, hp, hH, bind, Except.bind, pure, Except.pure]

theorem offsetArith4 (sign a b d u : Int) (hs : sign = 1 ∨ sign = -1) (h0 : 0 ≤ a) (h1 : a ≤ 23) (m0 : 0 ≤ b)
    (m1 : b ≤ 59) (s0 : 0 ≤ d) (s1 : d ≤ 59) (u0 : 0 ≤ u) (u1 : u ≤ 999999) :
    ∃ td off, deltaPy 0 d u 0 b a 0 = .ok td ∧ td.mulPy sign = .ok off ∧
      timezonePy off = .ok (sign * ((a * 3600 + b * 60 + d) * 1000000 + u)) := by
  have hT : totalUs 0 d u 0 b a 0 = (a * 3600 + b * 60 + d) * 1000000 + u := by unfold totalUs; omega
  obtain ⟨td, htd⟩ := (mkDeltaPy_spec ((a * 3600 + b * 60 + d) * 1000000 + u)).2.1.mpr
    (by unfold MIN_US END_US; omega)
  have hv := (mkDeltaPy_spec _).1 td htd
  have hmul : td.mulPy sign = mkDeltaPy (sign * ((a * 3600 + b * 60 + d) * 1000000 + u)) := by
    unfold Delta.mulPy
    rw [deltaPy_eq, mul_total, hv.2]
  obtain ⟨off, hoff⟩ := (mkDeltaPy_spec (sign * ((a * 3600 + b * 60 + d) * 1000000 + u))).2.1.mpr (by
    unfold MIN_US END_US; rcases hs with rfl | rfl <;> omega)
  have hv2 := (mkDeltaPy_spec _).1 off hoff
  refine ⟨td, off, by rw [deltaPy_eq, hT]; exact htd, by rw [hmul]; exact hoff, ?_⟩
  unfold timezonePy
  rw [hv2.2]
  by_cases hz : sign * ((a * 3600 + b * 60 + d) * 1000000 + u) = 0
  · rw [if_pos hz, hz]
  · rw [if_neg hz, if_pos (by rcases hs with rfl | rfl <;> omega)]

theorem tz_setup (t tz : List Char) (c : Char) (hc : c = '+' ∨ c = '-') (ha : isAsciiStr t = true)
    (hza : isAsciiStr tz = true) (hd : NoDesig t) (hzd : NoDesig tz) :
    isAsciiStr (t ++ c :: tz) = true ∧
    (if findPlusOne (t ++ c :: tz) '-' ≠ 0 then findPlusOne (t ++ c :: tz) '-' else
      let b' := findPlusOne (t ++ c :: tz) '+'
      if b' ≠ 0 then b' else findPlusOne (t ++ c :: tz) 'Z') = t.length + 1 := by
  refine ⟨?_, ?_⟩
  · unfold isAsciiStr at *; simp at ha hza ⊢
    refine ⟨ha, ?_, hza⟩; rcases hc with rfl | rfl <;> decide
  · rcases hc with rfl | rfl
    · have f1 := findPlusOne_none (t ++ '+' :: tz) '-' (fun x hx => by
        simp at hx; rcases hx with hx | hx | hx
        · exact (hd x hx).1
        · subst hx; decide
        · exact (hzd x hx).1)
      have f2 := findPlusOne_at t tz '+' (fun x hx => (hd x hx).2.1)
      simp [f1, f2]
    · have f1 := findPlusOne_at t tz '-' (fun x hx => (hd x hx).1)
      simp [f1]

theorem tz_off (t tz : List Char) (c : Char) (hc : c = '+' ∨ c = '-') (ha : isAsciiStr t = true)
    (hl : 2 ≤ t.length) (hd : NoDesig t) (hza : isAsciiStr tz = true) (hzd : NoDesig tz)
    (hzl : ¬ (tz.length = 0 ∨ tz.length = 1 ∨ tz.length = 3))
    (H M S U : Int) (hp : parseHHMMSSFFPy t = .ok (H, M, S, U)) (hH : H ≠ 24)
    (a b d u : Int) (hq : parseHHMMSSFFPy tz = .ok (a, b, d, u)) :
    parseIsoTimePy (t ++ c :: tz) =
      if a = 0 ∧ b = 0 ∧ d = 0 ∧ u = 0 then .ok (⟨H, M, S, U, some 0⟩, false, false, none)
      else match checkTime a b d u with
        | .error e => .ok (⟨H, M, S, U, none⟩, false, false, some e)
        | .ok _ => .ok (⟨H, M, S, U, some ((if c = '-' then -1 else 1) *
            ((a * 3600 + b * 60 + d) * 1000000 + u))⟩, false, false, none) := by
  obtain ⟨ha', htz⟩ := tz_setup t tz c hc ha hza hd hzd
  have htake : (t ++ c :: tz).take (t.length + 1 - 1) = t := by simp
  have hdrop : (t ++ c :: tz).drop (t.length + 1) = tz := by simp
  have hch : charAt (t ++ c :: tz) (t.length + 1 - 1) = c := by simp [charAt]
  have hcz : c ≠ 'Z' := by rcases hc with rfl | rfl <;> decide
  have hz0 : tz.length ≠ 0 := fun h => hzl (Or.inl h)
  have hne : t.length + 1 ≠ (t ++ c :: tz).length := by
    simp only [List.length_append, List.length_cons]; omega
  have hlen : ¬ (t ++ c :: tz).length < 2 := by simp only [List.length_append, List.length_cons]; omega
  have hgt : t.length + 1 > 0 := by omega
  unfold parseIsoTimePy
  simp only [hlen, ha', htz, htake, hdrop, hch, hp, hq, hH, hgt, hzl, hcz, ↓reduceIte, Bool.not_true,
    Bool.false_eq_true, or_false, false_and, hne]
  have hs : (if c = '-' then (-1 : Int) else 1) = 1 ∨ (if c = '-' then (-1 : Int) else 1) = -1 := by
    by_cases h : c = '-' <;> simp [h]
  by_cases hz : a = 0 ∧ b = 0 ∧ d = 0 ∧ u = 0
  · simp [hz, hH, bind, Except.bind, pure, Except.pure]
  · cases hck : checkTime a b d u with
    | error x => simp [hz, hck, hH, bind, Except.bind, pure, Except.pure]
    | ok q =>
      have hb : 0 ≤ a ∧ a ≤ 23 ∧ 0 ≤ b ∧ b ≤ 59 ∧ 0 ≤ d ∧ d ≤ 59 ∧ 0 ≤ u ∧ u ≤ 999999 := by
        unfold checkTime at hck
        split at hck
        · cases hck
        · split at hck
          · cases hck
          · split at hck
            · cases hck
            · split at hck
              · cases hck
              · omega
      obtain ⟨td, off, h1, h2, h3⟩ := offsetArith4 _ a b d u hs hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1
        hb.2.2.2.2.1 hb.2.2.2.2.2.1 hb.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2
      simp [hz, hck, hH, h1, h2, h3, bind, Except.bind, pure, Except.pure]

theorem tz_pre24 (t : List Char) (ha : isAsciiStr t = true) (hl : 2 ≤ t.length) (hd : NoDesig t)
    (M S U : Int) (hp : parseHHMMSSFFPy t = .ok (24, M, S, U)) :
    parseIsoTimePy t = .ok (if M = 0 ∧ S = 0 ∧ U = 0 then (⟨0, 0, 0, 0, none⟩, true, false, none)
      else (⟨24, M, S, U, none⟩, false, true, none)) := by
  have f1 := findPlusOne_none t '-' (fun x hx => (hd x hx).1)
  have f2 := findPlusOne_none t '+' (fun x hx => (hd x hx).2.1)
  have f3 := findPlusOne_none t 'Z' (fun x hx => (hd x hx).2.2)
  have h0 : ¬ (0 = t.length) := by omega
  unfold parseIsoTimePy
  by_cases hz : M = 0 ∧ S = 0 ∧ U = 0
  · obtain ⟨rfl, rfl, rfl⟩ := hz
    simp [show ¬ t.length < 2 by omega, ha, f1, f2, f3, hp, h0, bind, Except.bind, pure, Except.pure]
  · simp [show ¬ t.length < 2 by omega, ha, f1, f2, f3, hp, hz, h0, bind, Except.bind, pure, Except.pure]

theorem tz_err (t : List Char) (ha : isAsciiStr t = true) (hl : 2 ≤ t.length) (hd : NoDesig t)
    (e : PyExc) (hp : parseHHMMSSFFPy t = .error e) : parseIsoTimePy t = .error e := by
  have f1 := findPlusOne_none t '-' (fun x hx => (hd x hx).1)
  have f2 := findPlusOne_none t '+' (fun x hx => (hd x hx).2.1)
  have f3 := findPlusOne_none t 'Z' (fun x hx => (hd x hx).2.2)
  unfold parseIsoTimePy
  simp [show ¬ t.length < 2 by omega, ha, f1, f2, f3, hp, bind, Except.bind]

theorem tz_malformed (t tz : List Char) (c : Char) (hc : c = '+' ∨ c = '-') (ha : isAsciiStr t = true)
    (hl : 2 ≤ t.length) (hd : NoDesig t) (hza : isAsciiStr tz = true) (hzd : NoDesig tz)
    (hzl : tz.length = 0 ∨ tz.length = 1 ∨ tz.length = 3)
    (H M S U : Int) (hp : parseHHMMSSFFPy t = .ok (H, M, S, U)) :
    parseIsoTimePy (t ++ c :: tz) = .error (.valueError "Malformed time zone string") := by
  obtain ⟨ha', htz⟩ := tz_setup t tz c hc ha hza hd hzd
  have htake : (t ++ c :: tz).take (t.length + 1 - 1) = t := by simp
  have hdrop : (t ++ c :: tz).drop (t.length + 1) = tz := by simp
  have hcz : c ≠ 'Z' := by rcases hc with rfl | rfl <;> decide
  have hlen : ¬ (t ++ c :: tz).length < 2 := by simp only [List.length_append, List.length_cons]; omega
  have hgt : t.length + 1 > 0 := by omega
  have hlast : ¬ (t.length + 1 = (t ++ c :: tz).length ∧ (t ++ c :: tz).getLast? = some 'Z') := by
    rintro ⟨h1, h2⟩
    have h0 : tz = [] := by
      simp only [List.length_append, List.length_cons] at h1
      exact List.length_eq_zero_iff.mp (by omega)
    subst h0; simp at h2; exact hcz h2
  have hm : tz.length = 0 ∨ tz.length = 1 ∨ tz.length = 3 ∨ charAt (t ++ c :: tz) (t.length + 1 - 1) = 'Z' := by
    rcases hzl with h | h | h <;> simp [h]
  unfold parseIsoTimePy
  simp only [hlen, ha', htz, htake, hdrop, hp, hgt, hm, hlast, ↓reduceIte, Bool.not_true,
    Bool.false_eq_true, true_or]
  simp [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]

theorem tz_Zmore (t tz : List Char) (ha : isAsciiStr t = true) (hl : 2 ≤ t.length) (hd : NoDesig t)
    (hza : isAsciiStr tz = true) (hzd : NoDesig tz) (hne : tz ≠ [])
    (H M S U : Int) (hp : parseHHMMSSFFPy t = .ok (H, M, S, U)) :
    parseIsoTimePy (t ++ 'Z' :: tz) = .error (.valueError "Malformed time zone string") := by
  have f1 := findPlusOne_none (t ++ 'Z' :: tz) '-' (fun x hx => by
    simp at hx; rcases hx with hx | hx | hx
    · exact (hd x hx).1
    · subst hx; decide
    · exact (hzd x hx).1)
  have f2 := findPlusOne_none (t ++ 'Z' :: tz) '+' (fun x hx => by
    simp at hx; rcases hx with hx | hx | hx
    · exact (hd x hx).2.1
    · subst hx; decide
    · exact (hzd x hx).2.1)
  have f3 := findPlusOne_at t tz 'Z' (fun x hx => (hd x hx).2.2)
  have ha' : isAsciiStr (t ++ 'Z' :: tz) = true := by
    unfold isAsciiStr at *; simp at ha hza ⊢; exact ⟨ha, hza⟩
  have htake : (t ++ 'Z' :: tz).take (t.length + 1 - 1) = t := by simp
  have hdrop : (t ++ 'Z' :: tz).drop (t.length + 1) = tz := by simp
  have hch : charAt (t ++ 'Z' :: tz) (t.length + 1 - 1) = 'Z' := by simp [charAt]
  have hz0 : tz.length ≠ 0 := by simpa using hne
  have hne' : ¬ (t.length + 1 = (t ++ 'Z' :: tz).length ∧ (t ++ 'Z' :: tz).getLast? = some 'Z') := by
    rintro ⟨h1, -⟩
    simp only [List.length_append, List.length_cons] at h1; omega
  have hlen : ¬ (t ++ 'Z' :: tz).length < 2 := by simp only [List.length_append, List.length_cons]; omega
  have hgt : t.length + 1 > 0 := by omega
  have htz : (if findPlusOne (t ++ 'Z' :: tz) '-' ≠ 0 then findPlusOne (t ++ 'Z' :: tz) '-' else
      let b' := findPlusOne (t ++ 'Z' :: tz) '+'
      if b' ≠ 0 then b' else findPlusOne (t ++ 'Z' :: tz) 'Z') = t.length + 1 := by
    simp [f1, f2, f3]
  unfold parseIsoTimePy
  simp only [hlen, ha', htz, htake, hdrop, hch, hp, hne', hgt, ↓reduceIte, Bool.not_true,
    Bool.false_eq_true, or_true]
  simp [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]

theorem checkTime_err_class (a b d u : Int) (e : PyExc) (h : checkTime a b d u = .error e) :
    e.className = "ValueError" := by
  unfold checkTime at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · split at h
      · cases h; rfl
      · split at h
        · cases h; rfl
        · cases h

theorem checkTime_err_of (a b d u : Int)
    (h : ¬ (0 ≤ a ∧ a ≤ 23 ∧ 0 ≤ b ∧ b ≤ 59 ∧ 0 ≤ d ∧ d ≤ 59 ∧ 0 ≤ u ∧ u ≤ 999999)) :
    ∃ e, checkTime a b d u = .error e := by
  unfold checkTime
  split
  · exact ⟨_, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · exfalso; omega

/-- `_parse_isoformat_time(s)` for every time part `t` (ASCII, at least two characters, no
`-`, `+` or `Z`) whose `_parse_hh_mm_ss_ff(t)` is `(H, M, S, U)`, and every offset text `tz`
(ASCII, no designator):
- `t` alone is the naive time; `t + 'Z'` is the time with `timezone.utc` (:483-484);
- `t + c + tz` with `c` in `+-`: an offset of length 0, 1 or 3 is `Malformed time zone
  string` (:496-497); otherwise, with `_parse_hh_mm_ss_ff(tz) = (a, b, d, u)`, an all-zero
  offset is `timezone.utc` (:501-502), a valid one (hour 0..23, minute and second 0..59,
  microsecond 0..999999) is `c * (((a * 3600 + b * 60 + d) * 10**6) + u)` microseconds
  (:503-517), and an invalid one leaves no tzinfo and returns the `ValueError` of
  `_check_time_fields` as `error_from_tz` (:510-511);
- `t + 'Z' + tz` with a nonempty `tz` is `Malformed time zone string`;
- hour 24 (no offset): `24:00[:00[.0]]` becomes hour 0 with `became_next_day`, any other
  hour-24 time sets `error_from_components` (:471-478);
- an exception of `_parse_hh_mm_ss_ff(t)` propagates.
Hours other than 24 are assumed in the offset clauses, where the hour-24 flags are the same as
without an offset. -/
def ParseIsoTimeForms : Prop :=
  ∀ (t tz : List Char) (c : Char) (H M S U a b d u : Int) (e : PyExc),
    isAsciiStr t = true → 2 ≤ t.length → NoDesig t →
    (parseHHMMSSFFPy t = .ok (H, M, S, U) → H ≠ 24 →
      parseIsoTimePy t = .ok (⟨H, M, S, U, none⟩, false, false, none) ∧
      parseIsoTimePy (t ++ ['Z']) = .ok (⟨H, M, S, U, some 0⟩, false, false, none) ∧
      ((c = '+' ∨ c = '-') → isAsciiStr tz = true → NoDesig tz →
        ((tz.length = 0 ∨ tz.length = 1 ∨ tz.length = 3) →
          parseIsoTimePy (t ++ c :: tz) = .error (.valueError "Malformed time zone string")) ∧
        (¬ (tz.length = 0 ∨ tz.length = 1 ∨ tz.length = 3) → parseHHMMSSFFPy tz = .ok (a, b, d, u) →
          ((a = 0 ∧ b = 0 ∧ d = 0 ∧ u = 0) →
            parseIsoTimePy (t ++ c :: tz) = .ok (⟨H, M, S, U, some 0⟩, false, false, none)) ∧
          ((0 ≤ a ∧ a ≤ 23 ∧ 0 ≤ b ∧ b ≤ 59 ∧ 0 ≤ d ∧ d ≤ 59 ∧ 0 ≤ u ∧ u ≤ 999999) →
            ¬ (a = 0 ∧ b = 0 ∧ d = 0 ∧ u = 0) →
            parseIsoTimePy (t ++ c :: tz) = .ok (⟨H, M, S, U,
              some ((if c = '-' then -1 else 1) * ((a * 3600 + b * 60 + d) * 1000000 + u))⟩, false, false, none)) ∧
          (¬ (0 ≤ a ∧ a ≤ 23 ∧ 0 ≤ b ∧ b ≤ 59 ∧ 0 ≤ d ∧ d ≤ 59 ∧ 0 ≤ u ∧ u ≤ 999999) →
            ∃ x, parseIsoTimePy (t ++ c :: tz) = .ok (⟨H, M, S, U, none⟩, false, false, some x) ∧
              x.className = "ValueError"))) ∧
      (tz ≠ [] → isAsciiStr tz = true → NoDesig tz →
        parseIsoTimePy (t ++ 'Z' :: tz) = .error (.valueError "Malformed time zone string"))) ∧
    (parseHHMMSSFFPy t = .ok (24, M, S, U) →
      parseIsoTimePy t = .ok (if M = 0 ∧ S = 0 ∧ U = 0 then (⟨0, 0, 0, 0, none⟩, true, false, none)
        else (⟨24, M, S, U, none⟩, false, true, none))) ∧
    (parseHHMMSSFFPy t = .error e → parseIsoTimePy t = .error e)

theorem parseIsoTimeForms_proven : ParseIsoTimeForms := by
  intro t tz c H M S U a b d u e ha hl hd
  refine ⟨fun hp hH => ⟨tz_pre t ha hl hd H M S U hp hH, tz_Z t ha hl hd H M S U hp hH,
    fun hc hza hzd => ⟨fun hzl => tz_malformed t tz c hc ha hl hd hza hzd hzl H M S U hp,
      fun hzl hq => ?_⟩, fun hne hza hzd => tz_Zmore t tz ha hl hd hza hzd hne H M S U hp⟩,
    fun hp => tz_pre24 t ha hl hd M S U hp, fun hp => tz_err t ha hl hd e hp⟩
  have ho := tz_off t tz c hc ha hl hd hza hzd hzl H M S U hp hH a b d u hq
  refine ⟨fun hz => by rw [ho, if_pos hz], fun hv hz => ?_, fun hv => ?_⟩
  · rw [ho, if_neg hz]
    have : checkTime a b d u = .ok (a, b, d, u) := by
      unfold checkTime; simp [hv]
    rw [this]
  · have hz : ¬ (a = 0 ∧ b = 0 ∧ d = 0 ∧ u = 0) := by omega
    obtain ⟨x, hx⟩ := checkTime_err_of a b d u hv
    rw [ho, if_neg hz, hx]
    exact ⟨x, rfl, checkTime_err_class a b d u x hx⟩

end PyLean.Datetime
