import PyLean.Datetime.IsoTimeProps
import PyLean.Datetime.WrapScanProps
import PyLean.Datetime.IsoFormsProps

/-!
Branches the earlier theorems left out (review 50b4b958): the end of `_wrap_strftime`'s scan
and the fuel it is given, the `len(dtstr) == 7` branch of
`_find_isoformat_datetime_separator`, and the two first refusals of `_parse_isoformat_time`
with hour 24 next to a `Z` or an offset.
-/

namespace PyLean.Datetime
open PyLean

/-! ### `_wrap_strftime`: the end of the format and the fuel -/

theorem wrapScan_fuel (env : TzEnv) (obj : StrfObj) (tt0 gyear mon day : Int) (norm : Bool) :
    ∀ (n m : Nat) (f : List Char), f.length ≤ n → f.length ≤ m →
      wrapScanPy env obj tt0 gyear mon day norm n f = wrapScanPy env obj tt0 gyear mon day norm m f := by
  intro n
  induction n with
  | zero =>
    intro m f h _
    cases f with
    | nil => cases m <;> rfl
    | cons => simp at h
  | succ n ih =>
    intro m f h1 h2
    cases m with
    | zero => cases f with
      | nil => rfl
      | cons => simp at h2
    | succ m =>
      cases f with
      | nil => rfl
      | cons c rest =>
        simp only [List.length_cons] at h1 h2
        have ih' : ∀ g : List Char, g.length ≤ rest.length →
            wrapScanPy env obj tt0 gyear mon day norm n g = wrapScanPy env obj tt0 gyear mon day norm m g :=
          fun g hg => ih m g (by omega) (by omega)
        rcases rest with _ | ⟨c2, rest2⟩
        · simp only [wrapScanPy, ih' [] (by simp)]
        · rcases rest2 with _ | ⟨c3, rest3⟩
          · simp only [wrapScanPy, ih' [] (by simp), ih' [c2] (by simp)]
          · simp only [wrapScanPy, ih' rest3 (by simp; omega), ih' (c3 :: rest3) (by simp),
              ih' (c2 :: c3 :: rest3) (by simp)]

/-- The end of `_wrap_strftime`'s scan (:225-292) and the fuel `wrapStrftimePy` gives it, for
every object, tzinfo environment and format: once the format is used up nothing is appended
(the `while i < n` loop exits, :226, and `"".join(newformat)` adds nothing, :294); the length of
the format is enough fuel, i.e. any larger fuel gives the same result, so the scan never stops
before the end (every step of the loop consumes at least one character); and
`_wrap_strftime(object, format, timetuple)` is that scan from the start of the format with the
year, month and day of `timetuple`. Together with `WrapScanDirectives`, which pins each step,
this fixes the whole format handed to `time.strftime`. -/
def WrapScanEnd : Prop :=
  ∀ (env : TzEnv) (obj : StrfObj) (tt0 gyear mon day : Int) (norm : Bool),
    (∀ n, wrapScanPy env obj tt0 gyear mon day norm n [] = .ok []) ∧
    (∀ (f : List Char) (n : Nat), f.length ≤ n →
      wrapScanPy env obj tt0 gyear mon day norm n f =
        wrapScanPy env obj tt0 gyear mon day norm f.length f) ∧
    (∀ (fmt : List Char) (tt : TimeTuple),
      wrapStrftimePy env obj fmt tt gyear norm =
        wrapScanPy env obj (tt.getD 0 0) gyear (tt.getD 1 0) (tt.getD 2 0) norm fmt.length fmt)

theorem wrapScanEnd_proven : WrapScanEnd := by
  intro env obj tt0 gyear mon day norm
  refine ⟨fun n => by cases n <;> rfl, fun f n h => wrapScan_fuel _ _ _ _ _ _ _ n f.length f h (Nat.le_refl _),
    fun _ _ => rfl⟩

/-! ### `_find_isoformat_datetime_separator`: length 7 -/

/-- `_find_isoformat_datetime_separator(dtstr)` for every string of length 7 is 7
(:303-304), whatever its characters: `2020-01`, `2020W01` and `2020-W1` alike are a date with
nothing after it (the only caller, `datetime.fromisoformat`, has refused shorter strings,
:1969-1970). -/
def FindSepLen7 : Prop :=
  ∀ s : List Char, s.length = 7 → findSepPy s = .ok 7

theorem findSepLen7_proven : FindSepLen7 := by
  intro s h
  unfold findSepPy
  simp [h]

/-! ### `_parse_isoformat_time`: first refusals and hour 24 with an offset -/

theorem tz_Z24 (t : List Char) (ha : isAsciiStr t = true) (hl : 2 ≤ t.length) (hd : NoDesig t)
    (M S U : Int) (hp : parseHHMMSSFFPy t = .ok (24, M, S, U)) :
    parseIsoTimePy (t ++ ['Z']) = .ok (if M = 0 ∧ S = 0 ∧ U = 0 then (⟨0, 0, 0, 0, some 0⟩, true, false, none)
      else (⟨24, M, S, U, some 0⟩, false, true, none)) := by
  have f1 := findPlusOne_none (t ++ ['Z']) '-' (fun x hx => by
    simp at hx; rcases hx with hx | hx; exact (hd x hx).1; subst hx; decide)
  have f2 := findPlusOne_none (t ++ ['Z']) '+' (fun x hx => by
    simp at hx; rcases hx with hx | hx; exact (hd x hx).2.1; subst hx; decide)
  have f3 := findPlusOne_at t [] 'Z' (fun x hx => (hd x hx).2.2)
  have ha' : isAsciiStr (t ++ ['Z']) = true := by
    unfold isAsciiStr at *; simp at ha ⊢; exact ha
  unfold parseIsoTimePy
  by_cases hz : M = 0 ∧ S = 0 ∧ U = 0
  · obtain ⟨rfl, rfl, rfl⟩ := hz
    simp [show ¬ t.length + 1 < 2 by omega, ha', f1, f2, f3, hp, bind, Except.bind, pure, Except.pure]
  · simp [show ¬ t.length + 1 < 2 by omega, ha', f1, f2, f3, hp, hz, bind, Except.bind, pure, Except.pure]

theorem tz_off24 (t tz : List Char) (c : Char) (hc : c = '+' ∨ c = '-') (ha : isAsciiStr t = true)
    (hl : 2 ≤ t.length) (hd : NoDesig t) (hza : isAsciiStr tz = true) (hzd : NoDesig tz)
    (hzl : ¬ (tz.length = 0 ∨ tz.length = 1 ∨ tz.length = 3))
    (M S U : Int) (hp : parseHHMMSSFFPy t = .ok (24, M, S, U))
    (a b d u : Int) (hq : parseHHMMSSFFPy tz = .ok (a, b, d, u)) :
    let H' : Int := if M = 0 ∧ S = 0 ∧ U = 0 then 0 else 24
    let nd : Bool := decide (M = 0 ∧ S = 0 ∧ U = 0)
    let ec : Bool := !decide (M = 0 ∧ S = 0 ∧ U = 0)
    parseIsoTimePy (t ++ c :: tz) =
      if a = 0 ∧ b = 0 ∧ d = 0 ∧ u = 0 then .ok (⟨H', M, S, U, some 0⟩, nd, ec, none)
      else match checkTime a b d u with
        | .error e => .ok (⟨H', M, S, U, none⟩, nd, ec, some e)
        | .ok _ => .ok (⟨H', M, S, U, some ((if c = '-' then -1 else 1) *
            ((a * 3600 + b * 60 + d) * 1000000 + u))⟩, nd, ec, none) := by
  intro H' nd ec
  obtain ⟨ha', htz⟩ := tz_setup t tz c hc ha hza hd hzd
  have htake : (t ++ c :: tz).take (t.length + 1 - 1) = t := by simp
  have hdrop : (t ++ c :: tz).drop (t.length + 1) = tz := by simp
  have hch : charAt (t ++ c :: tz) (t.length + 1 - 1) = c := by simp [charAt]
  have hcz : c ≠ 'Z' := by rcases hc with rfl | rfl <;> decide
  have hne : t.length + 1 ≠ (t ++ c :: tz).length := by
    simp only [List.length_append, List.length_cons]; omega
  have hlen : ¬ (t ++ c :: tz).length < 2 := by simp only [List.length_append, List.length_cons]; omega
  have hgt : t.length + 1 > 0 := by omega
  have hflags : (if (24 : Int) = 24 then
      (if M = 0 ∧ S = 0 ∧ U = 0 then ((0 : Int), true, false) else ((24 : Int), false, true))
      else ((24 : Int), false, false)) = (H', nd, ec) := by
    simp only [H', nd, ec, ite_true]
    by_cases h : M = 0 ∧ S = 0 ∧ U = 0 <;> simp [h]
  unfold parseIsoTimePy
  simp only [hlen, ha', htz, htake, hdrop, hch, hp, hq, hgt, hzl, hcz, ↓reduceIte, Bool.not_true,
    Bool.false_eq_true, or_false, false_and, hne]
  have hs : (if c = '-' then (-1 : Int) else 1) = 1 ∨ (if c = '-' then (-1 : Int) else 1) = -1 := by
    by_cases h : c = '-' <;> simp [h]
  simp only [bind, Except.bind, pure, Except.pure] at hflags ⊢
  rw [hflags]
  by_cases hz : a = 0 ∧ b = 0 ∧ d = 0 ∧ u = 0
  · simp [hz]
  · cases hck : checkTime a b d u with
    | error x => simp [hz]
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
      simp [hz, h1, h2, h3]

/-- The first two refusals of `_parse_isoformat_time(tstr)` (:455-459) for every string: fewer
than two characters is `Isoformat time too short`, and otherwise a character outside ASCII
(code point 128 or more) is `Invalid isoformat string`, before any parsing. And hour 24 next to
a time zone, for every time part `t` and offset text `tz` as in `ParseIsoTimeForms`: the
hour-24 flags (:471-478) are set before the offset is looked at and are the same as without
one, so `24:00Z` and `24:00+01:00` are midnight with `became_next_day` and the zone kept, and
any other hour-24 time keeps hour 24 and sets `error_from_components`, with the offset parsed
as usual. -/
def ParseIsoTimeEdges : Prop :=
  ∀ (t tz : List Char) (c : Char) (M S U a b d u : Int),
    (t.length < 2 → parseIsoTimePy t = .error (.valueError "Isoformat time too short")) ∧
    (2 ≤ t.length → (∃ x ∈ t, 128 ≤ x.toNat) →
      parseIsoTimePy t = .error (.valueError "Invalid isoformat string")) ∧
    (isAsciiStr t = true → 2 ≤ t.length → NoDesig t → parseHHMMSSFFPy t = .ok (24, M, S, U) →
      let H' : Int := if M = 0 ∧ S = 0 ∧ U = 0 then 0 else 24
      let nd : Bool := decide (M = 0 ∧ S = 0 ∧ U = 0)
      let ec : Bool := !decide (M = 0 ∧ S = 0 ∧ U = 0)
      parseIsoTimePy (t ++ ['Z']) = .ok (⟨H', M, S, U, some 0⟩, nd, ec, none) ∧
      ((c = '+' ∨ c = '-') → isAsciiStr tz = true → NoDesig tz →
        ¬ (tz.length = 0 ∨ tz.length = 1 ∨ tz.length = 3) → parseHHMMSSFFPy tz = .ok (a, b, d, u) →
        ((a = 0 ∧ b = 0 ∧ d = 0 ∧ u = 0) →
          parseIsoTimePy (t ++ c :: tz) = .ok (⟨H', M, S, U, some 0⟩, nd, ec, none)) ∧
        ((0 ≤ a ∧ a ≤ 23 ∧ 0 ≤ b ∧ b ≤ 59 ∧ 0 ≤ d ∧ d ≤ 59 ∧ 0 ≤ u ∧ u ≤ 999999) →
          ¬ (a = 0 ∧ b = 0 ∧ d = 0 ∧ u = 0) →
          parseIsoTimePy (t ++ c :: tz) = .ok (⟨H', M, S, U,
            some ((if c = '-' then -1 else 1) * ((a * 3600 + b * 60 + d) * 1000000 + u))⟩, nd, ec, none)) ∧
        (¬ (0 ≤ a ∧ a ≤ 23 ∧ 0 ≤ b ∧ b ≤ 59 ∧ 0 ≤ d ∧ d ≤ 59 ∧ 0 ≤ u ∧ u ≤ 999999) →
          ∃ x, parseIsoTimePy (t ++ c :: tz) = .ok (⟨H', M, S, U, none⟩, nd, ec, some x) ∧
            x.className = "ValueError")))

theorem parseIsoTimeEdges_proven : ParseIsoTimeEdges := by
  intro t tz c M S U a b d u
  refine ⟨fun h => ?_, fun h hx => ?_, fun ha hl hd hp => ?_⟩
  · unfold parseIsoTimePy; simp [h, bind, Except.bind, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]
  · have hna : isAsciiStr t = false := by
      obtain ⟨x, hm, hx⟩ := hx
      unfold isAsciiStr
      rw [Bool.eq_false_iff]
      intro hall
      have := List.all_eq_true.mp hall x hm
      simp at this; omega
    unfold parseIsoTimePy
    simp [show ¬ t.length < 2 by omega, hna, bind, Except.bind, throw, throwThe, MonadExcept.throw,
      MonadExceptOf.throw]
  · intro H' nd ec
    refine ⟨?_, fun hc hza hzd hzl hq => ?_⟩
    · rw [tz_Z24 t ha hl hd M S U hp]
      by_cases h : M = 0 ∧ S = 0 ∧ U = 0
      · obtain ⟨rfl, rfl, rfl⟩ := h; simp [H', nd, ec]
      · simp [H', nd, ec, h]; intro h1 h2 h3; exact h ⟨h1, h2, h3⟩
    · have ho := tz_off24 t tz c hc ha hl hd hza hzd hzl M S U hp a b d u hq
      simp only at ho
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
