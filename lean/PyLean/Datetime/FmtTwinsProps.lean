import PyLean.Datetime.IsoRoundtrip
import PyLean.Datetime.TwinsProps

/-!
The text of `date.isoformat()`, `_format_time` and `_format_offset`, character by
character, and its agreement with the separately mirrored C formatters (`date_isoformat`,
`datetime_time_isoformat_impl`, `format_utcoffset`).
-/

namespace PyLean.Datetime

open PyLean

theorem padNat3 (n : Nat) (h : n < 1000) : padNat 3 n = [dc (n / 100), dc (n / 10 % 10), dc (n % 10)] := by
  rw [padNat_step 3 n (by omega), padNat_step 2 _ (by omega), padNat_one _ (by omega)]
  simp only [List.cons_append, List.nil_append]
  rw [show n / 10 / 10 = n / 100 by omega]

/-- Two decimal digits of `n`. -/
def d2 (n : Nat) : List Char := [dc (n / 10), dc (n % 10)]
/-- Three decimal digits of `n`. -/
def d3 (n : Nat) : List Char := [dc (n / 100), dc (n / 10 % 10), dc (n % 10)]
/-- Six decimal digits of `n`. -/
def d6 (n : Nat) : List Char :=
  [dc (n / 100000), dc (n / 10000 % 10), dc (n / 1000 % 10), dc (n / 100 % 10), dc (n / 10 % 10), dc (n % 10)]

theorem padInt_d2 (n : Int) (h0 : 0 ≤ n) (h1 : n < 100) : padInt 2 n = d2 n.toNat := by
  unfold padInt; rw [if_neg (by omega), padNat2 _ (by omega)]; rfl

theorem padInt_d3 (n : Int) (h0 : 0 ≤ n) (h1 : n < 1000) : padInt 3 n = d3 n.toNat := by
  unfold padInt; rw [if_neg (by omega), padNat3 _ (by omega)]; rfl

theorem padInt_d6 (n : Int) (h0 : 0 ≤ n) (h1 : n < 1000000) : padInt 6 n = d6 n.toNat := by
  unfold padInt; rw [if_neg (by omega), padNat6 _ (by omega)]; rfl

theorem fmt0_toList (w : Nat) (n : Int) : (fmt0 w n).toList = padInt w n := by
  unfold fmt0; exact String.toList_ofList

/-! ### `date.isoformat()` -/

/-- `date.isoformat()` of a valid date is `YYYY-MM-DD`: four digits of the year, `-`, two of
the month, `-`, two of the day, and C `date_isoformat` gives the same text. A basic-format
`YYYYMMDD`, a wrong padding or field order fails. -/
def DateIsoformatText : Prop :=
  ∀ y m d : Int, ValidDate y m d →
    dateIsoformat y m d =
      [dc (y.toNat / 1000), dc (y.toNat / 100 % 10), dc (y.toNat / 10 % 10), dc (y.toNat % 10), '-',
       dc (m.toNat / 10), dc (m.toNat % 10), '-', dc (d.toNat / 10), dc (d.toNat % 10)] ∧
    dateIsoformatC y m d = dateIsoformat y m d

theorem dateIsoformatText_proven : DateIsoformatText := by
  intro y m d h
  refine ⟨dateIsoformat_eq y m d h, ?_⟩
  unfold dateIsoformatC dateIsoformat
  simp only [String.toList_append, fmt0_toList, List.append_assoc]
  rfl

/-! ### `_format_time` -/

/-- The text `_format_time(hh, mm, ss, us, timespec)` documents: `HH`, `HH:MM`, `HH:MM:SS`,
`HH:MM:SS.sss` (milliseconds, truncated) or `HH:MM:SS.ffffff`, with `auto` choosing
microseconds exactly when `us != 0`. -/
def timeText (hh mm ss us : Int) : TimeSpec → List Char
  | .hours => d2 hh.toNat
  | .minutes => d2 hh.toNat ++ ':' :: d2 mm.toNat
  | .seconds => d2 hh.toNat ++ ':' :: d2 mm.toNat ++ ':' :: d2 ss.toNat
  | .milliseconds => d2 hh.toNat ++ ':' :: d2 mm.toNat ++ ':' :: d2 ss.toNat ++ '.' :: d3 (us / 1000).toNat
  | .microseconds => d2 hh.toNat ++ ':' :: d2 mm.toNat ++ ':' :: d2 ss.toNat ++ '.' :: d6 us.toNat
  | .auto => if us = 0 then d2 hh.toNat ++ ':' :: d2 mm.toNat ++ ':' :: d2 ss.toNat
      else d2 hh.toNat ++ ':' :: d2 mm.toNat ++ ':' :: d2 ss.toNat ++ '.' :: d6 us.toNat

/-- `_format_time` of valid fields is that text for every `timespec`, and the C formatter of
`time.isoformat`/`datetime.isoformat` gives the same text. -/
def FormatTimeText : Prop :=
  ∀ (hh mm ss us : Int) (spec : TimeSpec),
    0 ≤ hh → hh ≤ 23 → 0 ≤ mm → mm ≤ 59 → 0 ≤ ss → ss ≤ 59 → 0 ≤ us → us ≤ 999999 →
    formatTime hh mm ss us spec = timeText hh mm ss us spec ∧
    formatTimeC hh mm ss us spec = formatTime hh mm ss us spec

theorem formatTimeText_proven : FormatTimeText := by
  intro hh mm ss us spec h1 h2 h3 h4 h5 h6 h7 h8
  have eh := padInt_d2 hh h1 (by omega)
  have em := padInt_d2 mm h3 (by omega)
  have es := padInt_d2 ss h5 (by omega)
  have eu := padInt_d6 us h7 (by omega)
  have ems := padInt_d3 (us / 1000) (by omega) (by omega)
  have et : us.tdiv 1000 = us / 1000 := Int.tdiv_eq_ediv_of_nonneg h7
  cases spec with
  | auto =>
    by_cases hu : us = 0
    · unfold formatTime formatTimeC timeText
      simp [hu, fmt0_toList, String.toList_append, eh, em, es]
    · unfold formatTime formatTimeC timeText
      simp [hu, fmt0_toList, String.toList_append, eh, em, es, eu]
  | _ =>
    unfold formatTime formatTimeC timeText
    simp [fmt0_toList, String.toList_append, eh, em, es, eu, ems, et]

/-! ### `_format_offset` -/

/-- The text of `_format_offset(off, sep)` for an offset of `a` microseconds in absolute value
and the given sign: `±HH sep MM`, then `sep SS` when seconds or microseconds are nonzero,
then `.ffffff` when microseconds are nonzero. -/
def offsetText (sep : List Char) (neg : Bool) (a : Nat) : List Char :=
  let hh := a / 3600000000
  let mm := a % 3600000000 / 60000000
  let ss := a % 60000000 / 1000000
  let us := a % 1000000
  (if neg then '-' else '+') :: d2 hh ++ sep ++ d2 mm ++
    (if ss ≠ 0 ∨ us ≠ 0 then sep ++ d2 ss ++ (if us ≠ 0 then '.' :: d6 us else []) else [])

/-- `_format_offset(off, sep)` for every valid offset strictly inside ±24 hours is that text,
and C `format_utcoffset` (which negates the timedelta and splits its seconds field by
`divmod`) gives the same text. -/
def FormatOffsetText : Prop :=
  ∀ (sep : List Char) (t : Delta), t.Valid → -86400000000 < t.toUs → t.toUs < 86400000000 →
    formatOffsetSep sep (some t.toUs) = offsetText sep (decide (t.toUs < 0)) t.toUs.natAbs ∧
    formatUtcoffsetC sep (some t) = formatOffsetSep sep (some t.toUs)

theorem padNat_d2 (n : Nat) (h : n < 100) : padNat 2 n = d2 n := padNat2 n h
theorem padNat_d6 (n : Nat) (h : n < 1000000) : padNat 6 n = d6 n := padNat6 n h

theorem formatOffsetText_proven : FormatOffsetText := by
  intro sep t hv hlo hhi
  have py : formatOffsetSep sep (some t.toUs) = offsetText sep (decide (t.toUs < 0)) t.toUs.natAbs := by
    unfold formatOffsetSep offsetText
    have a1 : t.toUs.natAbs / 3600000000 < 100 := by omega
    have a2 : t.toUs.natAbs % 3600000000 / 60000000 < 100 := by omega
    have a3 : t.toUs.natAbs % 60000000 / 1000000 < 100 := by omega
    have a4 : t.toUs.natAbs % 1000000 < 1000000 := by omega
    have e1 : t.toUs.natAbs % 60000000 % 1000000 = t.toUs.natAbs % 1000000 := by omega
    simp only [padNat_d2 _ a1, padNat_d2 _ a2, padNat_d2 _ a3, e1, padNat_d6 _ a4]
    by_cases hn : t.toUs < 0 <;> by_cases h0 : t.toUs.natAbs % 60000000 = 0 <;>
      by_cases hss : t.toUs.natAbs % 60000000 / 1000000 = 0 <;>
      by_cases hu : t.toUs.natAbs % 1000000 = 0 <;> simp [hn, h0, hss, hu] <;> omega
  refine ⟨py, ?_⟩
  rw [py]
  unfold Delta.Valid MAX_DELTA_DAYS at hv
  -- The C side: the fields of the (negated) offset, in the shape of `format_utcoffset`.
  have key : ∃ (s u : Int) (c : Char), c = (if decide (t.toUs < 0) = true then '-' else '+') ∧
      0 ≤ s ∧ s < 86400 ∧ 0 ≤ u ∧ u < 1000000 ∧ s * 1000000 + u = t.toUs.natAbs ∧
      formatUtcoffsetC sep (some t) =
        (if u ≠ 0 then c :: padInt 2 (s / 60 / 60) ++ sep ++ padInt 2 (s / 60 % 60) ++ sep ++
            padInt 2 (s % 60) ++ ['.'] ++ padInt 6 u
         else if s % 60 ≠ 0 then c :: padInt 2 (s / 60 / 60) ++ sep ++ padInt 2 (s / 60 % 60) ++ sep ++
            padInt 2 (s % 60)
         else c :: padInt 2 (s / 60 / 60) ++ sep ++ padInt 2 (s / 60 % 60)) := by
    by_cases hd : t.days < 0
    · have hneg : t.negC = .ok ⟨0, (-t.toUs) / 1000000 % 86400, (-t.toUs) % 1000000⟩ := by
        unfold Delta.negC
        rw [newDeltaNormC_eq]
        have e : (-t.days * 86400 + -t.seconds) * 1000000 + -t.us = -t.toUs := by unfold Delta.toUs; omega
        rw [e]
        unfold mkDeltaN MAX_DELTA_DAYS Delta.toUs at *
        have hz : -((t.days * 86400 + t.seconds) * 1000000 + t.us) / 86400000000 = 0 := by omega
        rw [if_pos (by omega), hz]
      have htn : t.toUs < 0 := by unfold Delta.toUs; omega
      refine ⟨(-t.toUs) / 1000000 % 86400, (-t.toUs) % 1000000, '-', by simp [htn], by omega, by omega,
        by omega, by omega, by omega, ?_⟩
      unfold formatUtcoffsetC
      simp only [hd, ↓reduceIte, hneg]
    · have htn : ¬ t.toUs < 0 := by unfold Delta.toUs; omega
      have hd0 : t.days = 0 := by unfold Delta.toUs at hhi; omega
      refine ⟨t.seconds, t.us, '+', by simp [htn], by omega, by omega, by omega, by omega,
        by unfold Delta.toUs; omega, ?_⟩
      unfold formatUtcoffsetC
      simp only [hd, ↓reduceIte]
  obtain ⟨s, u, c, hc0, hs0, hs1, hu0, hu1, hsu, hc⟩ := key
  rw [hc]
  unfold offsetText
  have e1 : padInt 2 (s / 60 / 60) = d2 (t.toUs.natAbs / 3600000000) := by
    rw [padInt_d2 _ (by omega) (by omega)]; congr 1; omega
  have e2 : padInt 2 (s / 60 % 60) = d2 (t.toUs.natAbs % 3600000000 / 60000000) := by
    rw [padInt_d2 _ (by omega) (by omega)]; congr 1; omega
  have e3 : padInt 2 (s % 60) = d2 (t.toUs.natAbs % 60000000 / 1000000) := by
    rw [padInt_d2 _ (by omega) (by omega)]; congr 1; omega
  have e4 : padInt 6 u = d6 (t.toUs.natAbs % 1000000) := by
    rw [padInt_d6 _ (by omega) (by omega)]; congr 1; omega
  rw [e1, e2, e3, e4, ← hc0]
  by_cases hu : u = 0 <;> by_cases hss : s % 60 = 0 <;>
    by_cases hu' : t.toUs.natAbs % 1000000 = 0 <;>
    by_cases hss' : t.toUs.natAbs % 60000000 / 1000000 = 0 <;> simp [hu, hss, hu', hss'] <;> omega

/-! ### The `timespec` argument -/

/-- `isoformat(timespec=x)` refuses the same arguments with the same exception class in both
twins. -/
def TimespecTwins : Prop :=
  ∀ x : SpecArg, SameOutcome (parseTimespecArgPy x) (parseTimespecArgC x)

/-- `time(1).isoformat(timespec=1)`: Python's `specs[1]` raises `KeyError`, turned into
`ValueError('Unknown timespec value')`; C's `str` converter raises `TypeError`. -/
theorem timespecTwins_refuted : ¬TimespecTwins := by
  intro h
  have := h (.other true)
  simp [SameOutcome, parseTimespecArgPy, parseTimespecArgC, PyExc.className] at this

/-- For every `str` the twins give the same spec or the same `ValueError` (message included),
and an unhashable non-`str` is a `TypeError` in both. -/
def TimespecStr : Prop :=
  (∀ s : String, parseTimespecArgPy (.str s) = parseTimespecArgC (.str s)) ∧
  SameOutcome (parseTimespecArgPy (.other false)) (parseTimespecArgC (.other false))

theorem timespecStr_proven : TimespecStr := by
  refine ⟨fun s => ?_, by simp [SameOutcome, parseTimespecArgPy, parseTimespecArgC, PyExc.className]⟩
  by_cases h1 : s = "auto"
  · subst h1; decide
  by_cases h2 : s = "hours"
  · subst h2; decide
  by_cases h3 : s = "minutes"
  · subst h3; decide
  by_cases h4 : s = "seconds"
  · subst h4; decide
  by_cases h5 : s = "milliseconds"
  · subst h5; decide
  by_cases h6 : s = "microseconds"
  · subst h6; decide
  have hp : parseTimespec s = .error (.valueError "Unknown timespec value") := by
    unfold parseTimespec; split <;> simp_all
  have hc : specsC.find? (·.1 = s) = none := by
    simp [specsC, List.find?, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6]
  simp only [parseTimespecArgPy, parseTimespecArgC, hp, h1, ↓reduceIte, hc]

end PyLean.Datetime
