import PyLean.Datetime.IsoRoundtrip
import PyLean.Datetime.IsoRefute
import PyLean.Datetime.DeltaProps
import PyLean.Datetime.Strptime

/-!
Properties of what 3.15 changed in `fromisoformat` and `_strptime`: the fields of a UTC offset
are range-checked, fixed-width fields go through `_read_isoformat_component`, `%:z`, `%D` and
`%F` exist, `%z` is optional, and `%d` without a year is an error.
-/

namespace PyLean.Datetime

open PyLean

/-! ### The fields of a UTC offset -/

/-- `12:00` with an offset `±ab:ce` of four digits. -/
def offStr (neg : Bool) (a b c e : Nat) : List Char :=
  ['1', '2', ':', '0', '0', if neg then '-' else '+', dc a, dc b, ':', dc c, dc e]

/-- What both twins must do with that offset. -/
def offsetResult (neg : Bool) (hh mm : Int) : Py Int :=
  if ¬(0 ≤ hh ∧ hh ≤ 23) then .error (.valueError s!"hour must be in 0..23, not {hh}")
  else if ¬(0 ≤ mm ∧ mm ≤ 59) then .error (.valueError s!"minute must be in 0..59, not {mm}")
  else .ok ((if neg then -1 else 1) * ((hh * 3600 + mm * 60) * 1000000))

theorem offsetFieldsC (sg a b c e : Nat) (ha : a < 10) (hb : b < 10) (hc : c < 10) (he : e < 10) :
    parseHHMMSSFFC [49, 50, 58, 48, 48, sg, 48 + a, 48 + b, 58, 48 + c, 48 + e] 6 11 =
      { h := ((a * 10 + b : Nat) : Int), mi := ((c * 10 + e : Nat) : Int), rv := 0 } := by
  simp [parseHHMMSSFFC, parseDigitsC, byteAt, hhStep, byte_dc a ha, byte_dc b hb, byte_dc c hc, byte_dc e he]

theorem timeFieldsC (neg : Bool) (a b c e : Nat) :
    parseHHMMSSFFC [49, 50, 58, 48, 48, if neg then 45 else 43, 48 + a, 48 + b, 58, 48 + c, 48 + e] 0 5 =
      { h := 12, mi := 0, rv := 1 } := by
  cases neg <;> simp [parseHHMMSSFFC, parseDigitsC, byteAt, hhStep, isDigitC]

theorem utf8_offStr (neg : Bool) (a b c e : Nat) (ha : a < 10) (hb : b < 10) (hc : c < 10) (he : e < 10) :
    utf8 (offStr neg a b c e) =
      [49, 50, 58, 48, 48, if neg then 45 else 43, 48 + a, 48 + b, 58, 48 + c, 48 + e] := by
  have h := fun k hk => (dc_facts k hk).2.2.2.2.2.2.2.2.2.2
  have c1 : utf8Char '1' = [49] := by decide
  have c2 : utf8Char '2' = [50] := by decide
  have c3 : utf8Char ':' = [58] := by decide
  have c4 : utf8Char '0' = [48] := by decide
  have c5 : utf8Char '-' = [45] := by decide
  have c6 : utf8Char '+' = [43] := by decide
  cases neg <;> simp [utf8, offStr, h a ha, h b hb, h c hc, h e he, c1, c2, c3, c4, c5, c6]

theorem tzScan_off (neg : Bool) (a b c e : Nat) :
    tzScan [49, 50, 58, 48, 48, if neg then 45 else 43, 48 + a, 48 + b, 58, 48 + c, 48 + e] 0 11 = 5 := by
  cases neg <;> simp [tzScan, isTzDesignator, List.findIdx?_cons]

theorem tzinfo_ok (X : Int) (h0 : -86400 < X) (h1 : X < 86400) :
    tzinfoFromIsoResults 1 X 0 = .ok (some (X * 1000000)) := by
  unfold tzinfoFromIsoResults
  rw [if_pos rfl]
  by_cases hx : X = 0
  · subst hx; rfl
  · rw [if_neg (by simp [hx])]
    have hm : X * 1000000 ≠ 0 := by omega
    by_cases hp : 0 < X
    · have : newDeltaNormC 0 X 0 = .ok ⟨0, X, 0⟩ := by
        simp [newDeltaNormC, checkDeltaDayRange, MAX_DELTA_DAYS, show ¬ X < 0 by omega, show ¬ 86400 ≤ X by omega,
          bind, Except.bind, pure, Except.pure]
      simp [bind, Except.bind, this, newTimezoneC, Delta.toUs, hm, Functor.map, Except.map]
    · have : newDeltaNormC 0 X 0 = .ok ⟨-1, X + 86400, 0⟩ := by
        have e1 : X / 86400 = -1 := by omega
        have e2 : X % 86400 = X + 86400 := by omega
        simp [newDeltaNormC, checkDeltaDayRange, MAX_DELTA_DAYS, normalizePair, show X < 0 by omega, e1, e2,
          bind, Except.bind, pure, Except.pure]
      have e3 : (-86400 + (X + 86400)) * 1000000 = X * 1000000 := by omega
      simp [bind, Except.bind, this, newTimezoneC, Delta.toUs, Functor.map, Except.map, e3, hm,
        show X + 86400 ≠ 0 by omega]

theorem timeOffsetC (neg : Bool) (a b c e : Nat) (ha : a < 10) (hb : b < 10) (hc : c < 10) (he : e < 10) :
    timeFromIsoC (offStr neg a b c e) =
      (offsetResult neg ((a * 10 + b : Nat)) ((c * 10 + e : Nat))).map (fun o => (⟨12, 0, 0, 0, some o⟩ : TimeV)) := by
  have hr : parseIsoTimeC [49, 50, 58, 48, 48, if neg then 45 else 43, 48 + a, 48 + b, 58, 48 + c, 48 + e] 0 11 =
      match checkTime ((a * 10 + b : Nat) : Int) ((c * 10 + e : Nat) : Int) 0 0 with
      | .error x => { h := 12, mi := 0, s := 0, us := 0, tzoffset := 0, tzus := 0, rv := -6, err := some x }
      | .ok _ => { h := 12, mi := 0, s := 0, us := 0,
                   tzoffset := (if neg then -1 else 1) * (((a * 10 + b : Nat) : Int) * 3600 + ((c * 10 + e : Nat) : Int) * 60),
                   tzus := 0, rv := 1, err := none } := by
    unfold parseIsoTimeC
    simp only [Nat.zero_add, tzScan_off, timeFieldsC]
    cases neg <;> simp [byteAt, offsetFieldsC _ a b c e ha hb hc he] <;> (cases checkTime _ _ _ _ <;> rfl)
  unfold timeFromIsoC
  rw [utf8_offStr neg a b c e ha hb hc he]
  have hb0 : byteAt [49, 50, 58, 48, 48, if neg then 45 else 43, 48 + a, 48 + b, 58, 48 + c, 48 + e] 0 = 49 := rfl
  simp only [hb0, List.length_cons, List.length_nil]
  simp only [show ¬ (49 : Nat) = 84 by omega, if_false, Nat.zero_add]
  rw [show (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 : Nat) = 11 from rfl, hr]
  generalize hhh : ((a * 10 + b : Nat) : Int) = hh
  generalize hmm : ((c * 10 + e : Nat) : Int) = mm
  have h0 : 0 ≤ hh := by omega
  have m0 : 0 ≤ mm := by omega
  have hX := hhh
  have mX := hmm
  by_cases h1 : hh ≤ 23
  · by_cases h2 : mm ≤ 59
    · have hc : checkTime hh mm 0 0 = .ok (hh, mm, 0, 0) := by
        simp [checkTime, h0, h1, h2, m0]
      have ht : ∀ sign : Int, (sign = 1 ∨ sign = -1) →
          tzinfoFromIsoResults 1 (sign * (hh * 3600 + mm * 60)) 0 =
            .ok (some (sign * ((hh * 3600 + mm * 60) * 1000000))) := by
        intro sign hs
        rcases hs with rfl | rfl
        · have := tzinfo_ok (1 * (hh * 3600 + mm * 60)) (by omega) (by omega)
          rw [this]; congr 2; omega
        · have := tzinfo_ok (-1 * (hh * 3600 + mm * 60)) (by omega) (by omega)
          rw [this]; congr 2; omega
      rw [hc]
      have hs : (if neg = true then -1 else 1 : Int) = 1 ∨ (if neg = true then -1 else 1 : Int) = -1 := by
        cases neg <;> simp
      simp [offsetResult, h0, h1, h2, m0, ht _ hs, checkTime, bind, Except.bind, pure, Except.pure, Except.map]
    · have hc : checkTime hh mm 0 0 = .error (.valueError s!"minute must be in 0..59, not {mm}") := by
        simp [checkTime, h0, h1, h2]
      rw [hc]
      simp [offsetResult, h0, h1, h2, timeResError, bind, Except.bind, throw, throwThe, MonadExcept.throw,
        MonadExceptOf.throw, Except.map]
  · have hc : checkTime hh mm 0 0 = .error (.valueError s!"hour must be in 0..23, not {hh}") := by
      simp [checkTime, h0, h1]
    rw [hc]
    simp [offsetResult, h0, h1, timeResError, bind, Except.bind, throw, throwThe, MonadExcept.throw,
      MonadExceptOf.throw, Except.map]

/-! Python -/

theorem dc_ne (k : Nat) (hk : k < 10) : dc k ≠ '-' ∧ dc k ≠ '+' ∧ dc k ≠ 'Z' := by
  have : ∀ k : Fin 10, dc k ≠ '-' ∧ dc k ≠ '+' ∧ dc k ≠ 'Z' := by decide
  exact this ⟨k, hk⟩

theorem offsetFieldsPy (a b c e : Nat) (ha : a < 10) (hb : b < 10) (hc : c < 10) (he : e < 10) :
    parseHHMMSSFFPy [dc a, dc b, ':', dc c, dc e] =
      .ok (((a * 10 + b : Nat) : Int), ((c * 10 + e : Nat) : Int), 0, 0) := by
  have p1 := readIsoComponent_dc [a, b] (by simp) (by simp; omega)
  have p2 := readIsoComponent_dc [c, e] (by simp) (by simp; omega)
  simp only [List.map_cons, List.map_nil, digitsNat, List.foldl_cons, List.foldl_nil, List.length_cons,
    List.length_nil] at p1 p2
  unfold parseHHMMSSFFPy timeCompPy
  simp [slice, p1, p2, bind, Except.bind, pure, Except.pure]

theorem isAscii_offStr (neg : Bool) (a b c e : Nat) (ha : a < 10) (hb : b < 10) (hc : c < 10) (he : e < 10) :
    isAsciiStr (offStr neg a b c e) = true := by
  have hasc : ∀ k, k < 10 → (dc k).toNat < 128 := fun k hk => by rw [(dc_facts k hk).2.1]; omega
  cases neg <;> simp [isAsciiStr, offStr, hasc a ha, hasc b hb, hasc c hc, hasc e he]

theorem tzPos_offStr (neg : Bool) (a b c e : Nat) (ha : a < 10) (hb : b < 10) (hc : c < 10) (he : e < 10) :
    (if findPlusOne (offStr neg a b c e) '-' ≠ 0 then findPlusOne (offStr neg a b c e) '-' else
      let b' := findPlusOne (offStr neg a b c e) '+'
      if b' ≠ 0 then b' else findPlusOne (offStr neg a b c e) 'Z') = 6 := by
  have fa := dc_ne a ha
  have fb := dc_ne b hb
  have fc := dc_ne c hc
  have fe := dc_ne e he
  cases neg <;> simp [findPlusOne, offStr, List.findIdx?_cons, fa, fb, fc, fe]

/-- The arithmetic of the `else` branch, _pydatetime.py:513-515. -/
theorem offsetArithPy (sign hh mm : Int) (hs : sign = 1 ∨ sign = -1) (h0 : 0 ≤ hh) (h1 : hh ≤ 23) (m0 : 0 ≤ mm)
    (m1 : mm ≤ 59) :
    ∃ td off, deltaPy 0 0 0 0 mm hh 0 = .ok td ∧ td.mulPy sign = .ok off ∧
      timezonePy off = .ok (sign * ((hh * 3600 + mm * 60) * 1000000)) := by
  have hT : totalUs 0 0 0 0 mm hh 0 = (hh * 3600 + mm * 60) * 1000000 := by unfold totalUs; omega
  obtain ⟨td, htd⟩ := (mkDeltaPy_spec ((hh * 3600 + mm * 60) * 1000000)).2.1.mpr (by unfold MIN_US END_US; omega)
  have hv := (mkDeltaPy_spec _).1 td htd
  have hmul : td.mulPy sign = mkDeltaPy (sign * ((hh * 3600 + mm * 60) * 1000000)) := by
    unfold Delta.mulPy
    rw [deltaPy_eq, mul_total, hv.2]
  obtain ⟨off, hoff⟩ := (mkDeltaPy_spec (sign * ((hh * 3600 + mm * 60) * 1000000))).2.1.mpr (by
    unfold MIN_US END_US; rcases hs with rfl | rfl <;> omega)
  have hv2 := (mkDeltaPy_spec _).1 off hoff
  refine ⟨td, off, by rw [deltaPy_eq, hT]; exact htd, by rw [hmul]; exact hoff, ?_⟩
  unfold timezonePy
  rw [hv2.2]
  by_cases hz : sign * ((hh * 3600 + mm * 60) * 1000000) = 0
  · rw [if_pos hz, hz]
  · rw [if_neg hz, if_pos (by rcases hs with rfl | rfl <;> omega)]

theorem parseIsoTimeOffPy (neg : Bool) (a b c e : Nat) (ha : a < 10) (hb : b < 10) (hc : c < 10) (he : e < 10) :
    parseIsoTimePy (offStr neg a b c e) =
      match checkTime ((a * 10 + b : Nat) : Int) ((c * 10 + e : Nat) : Int) 0 0 with
      | .error x => .ok (⟨12, 0, 0, 0, none⟩, false, false, some x)
      | .ok _ => .ok (⟨12, 0, 0, 0, some ((if neg then -1 else 1) *
          ((((a * 10 + b : Nat) : Int) * 3600 + ((c * 10 + e : Nat) : Int) * 60) * 1000000))⟩, false, false, none) := by
  have hlen : (offStr neg a b c e).length = 11 := by cases neg <;> rfl
  have htake : (offStr neg a b c e).take 5 = ['1', '2', ':', '0', '0'] := by cases neg <;> rfl
  have hdrop : (offStr neg a b c e).drop 6 = [dc a, dc b, ':', dc c, dc e] := by cases neg <;> rfl
  have hch : charAt (offStr neg a b c e) 5 = (if neg then '-' else '+') := by cases neg <;> rfl
  have h12 : parseHHMMSSFFPy ['1', '2', ':', '0', '0'] = .ok (12, 0, 0, 0) := by decide
  have hz : (if neg then '-' else '+') ≠ 'Z' := by cases neg <;> decide
  have hm : (if neg then '-' else '+') = '-' ↔ neg = true := by cases neg <;> decide
  unfold parseIsoTimePy
  simp only [hlen, isAscii_offStr neg a b c e ha hb hc he, tzPos_offStr neg a b c e ha hb hc he, htake, hdrop,
    Nat.add_one_sub_one, offsetFieldsPy a b c e ha hb hc he]
  have bh : (0 : Int) ≤ ((a * 10 + b : Nat) : Int) := by omega
  have bm : (0 : Int) ≤ ((c * 10 + e : Nat) : Int) := by omega
  generalize ((a * 10 + b : Nat) : Int) = hh at bh ⊢
  generalize ((c * 10 + e : Nat) : Int) = mm at bm ⊢
  have hs : (if neg = true then -1 else 1 : Int) = 1 ∨ (if neg = true then -1 else 1 : Int) = -1 := by
    cases neg <;> simp
  by_cases hzero : hh = 0 ∧ mm = 0
  · obtain ⟨rfl, rfl⟩ := hzero
    simp [hch, hz, h12, checkTime, bind, Except.bind, pure, Except.pure]
  · cases hck : checkTime hh mm 0 0 with
    | error x =>
      simp [hch, hz, h12, hck, hzero, bind, Except.bind, pure, Except.pure]
    | ok q =>
      have hb : 0 ≤ hh ∧ hh ≤ 23 ∧ 0 ≤ mm ∧ mm ≤ 59 := by
        unfold checkTime at hck
        split at hck
        · cases hck
        · split at hck
          · cases hck
          · omega
      obtain ⟨td, off, h1, h2, h3⟩ := offsetArithPy _ hh mm hs hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
      simp [hch, hz, h12, hck, hzero, hm, h1, h2, h3, bind, Except.bind, pure, Except.pure]

theorem timeOffsetPy (neg : Bool) (a b c e : Nat) (ha : a < 10) (hb : b < 10) (hc : c < 10) (he : e < 10) :
    timeFromIsoPy (offStr neg a b c e) =
      (offsetResult neg ((a * 10 + b : Nat)) ((c * 10 + e : Nat))).map (fun o => (⟨12, 0, 0, 0, some o⟩ : TimeV)) := by
  have hstrip : removePrefixT (offStr neg a b c e) = offStr neg a b c e := by cases neg <;> rfl
  unfold timeFromIsoPy
  simp only [hstrip]
  rw [parseIsoTimeOffPy neg a b c e ha hb hc he]
  have h0 : (0 : Int) ≤ ((a * 10 + b : Nat) : Int) := by omega
  have m0 : (0 : Int) ≤ ((c * 10 + e : Nat) : Int) := by omega
  generalize ((a * 10 + b : Nat) : Int) = hh at h0 ⊢
  generalize ((c * 10 + e : Nat) : Int) = mm at m0 ⊢
  by_cases h1 : hh ≤ 23
  · by_cases h2 : mm ≤ 59
    · have hc' : checkTime hh mm 0 0 = .ok (hh, mm, 0, 0) := by simp [checkTime, h0, h1, h2, m0]
      rw [hc']
      simp [offsetResult, h0, h1, h2, m0, checkTime, bind, Except.bind, pure, Except.pure, Except.map]
    · have hc' : checkTime hh mm 0 0 = .error (.valueError s!"minute must be in 0..59, not {mm}") := by
        simp [checkTime, h0, h1, h2]
      rw [hc']
      simp [offsetResult, h0, h1, h2, bind, Except.bind, throw, throwThe, MonadExcept.throw,
        MonadExceptOf.throw, Except.map, pure, Except.pure]
  · have hc' : checkTime hh mm 0 0 = .error (.valueError s!"hour must be in 0..23, not {hh}") := by
      simp [checkTime, h0, h1]
    rw [hc']
    simp [offsetResult, h0, h1, bind, Except.bind, throw, throwThe, MonadExcept.throw,
      MonadExceptOf.throw, Except.map, pure, Except.pure]

/-- For a time with an offset `±HH:MM`, whichever two-digit values the offset's fields hold:
an hour above 23 or a minute above 59 raises the same `ValueError` in both twins, naming the
field, and every other offset gives that many microseconds. Until 3.14 neither twin checked
the fields, so `+05:60` was accepted as `+06:00`. -/
def FromisoOffsetRange : Prop :=
  ∀ (neg : Bool) (a b c e : Nat), a < 10 → b < 10 → c < 10 → e < 10 →
    timeFromIsoPy (offStr neg a b c e) =
      (offsetResult neg ((a * 10 + b : Nat)) ((c * 10 + e : Nat))).map (fun o => (⟨12, 0, 0, 0, some o⟩ : TimeV)) ∧
    timeFromIsoC (offStr neg a b c e) =
      (offsetResult neg ((a * 10 + b : Nat)) ((c * 10 + e : Nat))).map (fun o => (⟨12, 0, 0, 0, some o⟩ : TimeV))

theorem fromisoOffsetRange_proven : FromisoOffsetRange := fun neg a b c e ha hb hc he =>
  ⟨timeOffsetPy neg a b c e ha hb hc he, timeOffsetC neg a b c e ha hb hc he⟩

/-! ### `_read_isoformat_component` -/

/-- `_read_isoformat_component(s, n)` returns the value of `n` ASCII digits, and for an ASCII
`s` refuses everything else: another length, the empty string, and any character that is not a
digit, signs and spaces included, which `int()` alone would take. That `s` is ASCII is the
function's documented precondition (_pydatetime.py:359-360), and both callers check it. It is
needed: the real `str.isdigit` also takes non-ASCII digits, so `('١٢', 2)` returns 12. -/
def ReadIsoComponentExact : Prop :=
  (∀ l : List Nat, l ≠ [] → (∀ k ∈ l, k < 10) → readIsoComponent (l.map dc) l.length = .ok (digitsNat l)) ∧
  (∀ (s : List Char) (n : Nat), isAsciiStr s = true →
    (s.length ≠ n ∨ s = [] ∨ ∃ c ∈ s, isAsciiDigit c = false) →
    readIsoComponent s n = .error (.valueError "Invalid isoformat string"))

theorem readIsoComponentExact_proven : ReadIsoComponentExact := by
  refine ⟨readIsoComponent_dc, ?_⟩
  intro s n _ h
  unfold readIsoComponent
  rw [if_pos]
  rcases h with h | h | ⟨c, hc, hd⟩
  · exact Or.inl h
  · subst h; right; rfl
  · right
    have : s.all isAsciiDigit = false := by
      rw [List.all_eq_false]
      exact ⟨c, hc, by simp [hd]⟩
    simp [isDigitStr, this]

/-! ### `_strptime` -/

/-- The check after the match, _strptime.py:576-587, for a `found.end()` within the string: a
full match goes on, and otherwise it raises `ValueError`, never the `IndexError` of `rest[0]`
on an empty `rest`. The message blames a missing colon exactly when `%:z` matched something
and the rest does not start with one. -/
def StrptimeEndCheckExact : Prop :=
  ∀ (data : List Char) (endPos : Nat) (colonZ : Option (Option String)), endPos ≤ data.length →
    (data.length = endPos → strptimeEndCheck data endPos colonZ = .ok ()) ∧
    (data.length ≠ endPos → (data.drop endPos) ≠ [] ∧
      strptimeEndCheck data endPos colonZ = .error (.valueError (
        if colonZ.join.isSome ∧ (data.drop endPos).head? ≠ some ':' then
          s!"Missing colon in %:z before '{String.ofList (data.drop endPos)}', got '{String.ofList data}'"
        else s!"unconverted data remains: {String.ofList (data.drop endPos)}")))

theorem strptimeEndCheckExact_proven : StrptimeEndCheckExact := by
  intro data endPos colonZ hle
  constructor
  · intro h; simp [strptimeEndCheck, h]
  · intro h
    refine ⟨by simp [List.drop_eq_nil_iff]; omega, ?_⟩
    unfold strptimeEndCheck
    rw [if_pos h]
    rcases colonZ with _ | _ | g
    · simp
    · simp
    · by_cases hc : data[endPos]? = some ':' <;> simp [hc]

/-- `%z` and `%:z` read the same text the same way, and a group that did not take part leaves
the state as it was, so an absent offset gives a naive result. -/
def StrptimeZColon : Prop :=
  ∀ (lt : LocaleTimeV) (st : StrpState) (z : String),
    strpStep lt [("z", some z)] st "z" = strpStep lt [("colon_z", some z)] st "colon_z" ∧
    strpStep lt [("z", none)] st "z" = .ok st ∧ strpStep lt [("colon_z", none)] st "colon_z" = .ok st

theorem strptimeZColon_proven : StrptimeZColon := by
  intro lt st z
  refine ⟨?_, ?_, ?_⟩ <;> simp [strpStep, foundGet, pure, Except.pure]

/-! ### `TimeRE` -/

/-- `%D` and `%F` are the regexes of the formats they abbreviate, in every locale,
_strptime.py:424-425. -/
def TimeREAbbreviations : Prop :=
  ∀ (lt : LocaleTimeV) (m : List (String × String)), timeREMap lt = .ok m →
    m.lookup "D" = some "(?P<m>1[0-2]|0[1-9]|[1-9])/(?P<d>3[0-1]|[1-2]\\d|0[1-9]|[1-9]| [1-9])/(?P<y>\\d\\d)" ∧
    m.lookup "F" = some "(?P<Y>\\d\\d\\d\\d)-(?P<m>1[0-2]|0[1-9]|[1-9])-(?P<d>3[0-1]|[1-2]\\d|0[1-9]|[1-9]| [1-9])"

theorem timeREAdd_ok (m m' : List (String × String)) (k fmt : String) (h : timeREAdd m k fmt = .ok m') :
    ∃ p, timeREPattern (fun k => List.lookup k m) fmt = .ok p ∧ m' = (k, p) :: m := by
  unfold timeREAdd at h
  cases hp : timeREPattern (fun k => List.lookup k m) fmt with
  | error e => simp [hp, bind, Except.bind] at h
  | ok p =>
    simp [hp, bind, Except.bind, pure, Except.pure] at h
    exact ⟨p, rfl, h.symm⟩

set_option maxRecDepth 100000 in
theorem timeREAbbreviations_proven : TimeREAbbreviations := by
  intro lt m h
  unfold timeREMap at h
  simp only [bind, Except.bind] at h
  cases h1 : timeREAdd (timeREBase lt) "D" "%m/%d/%y" with
  | error e => simp [h1] at h
  | ok m1 =>
    simp only [h1] at h
    cases h2 : timeREAdd m1 "F" "%Y-%m-%d" with
    | error e => simp [h2] at h
    | ok m2 =>
      simp only [h2] at h
      cases h3 : timeREAdd m2 "T" "%H:%M:%S" with
      | error e => simp [h3] at h
      | ok m3 =>
        simp only [h3] at h
        cases h4 : timeREAdd m3 "R" "%H:%M" with
        | error e => simp [h4] at h
        | ok m4 =>
          simp only [h4] at h
          cases h5 : timeREAdd m4 "r" lt.lcTimeAmpm with
          | error e => simp [h5] at h
          | ok m5 =>
            simp only [h5] at h
            cases h6 : timeREAdd m5 "X" lt.lcTime with
            | error e => simp [h6] at h
            | ok m6 =>
              simp only [h6] at h
              cases h7 : timeREAdd m6 "x" lt.lcDate with
              | error e => simp [h7] at h
              | ok m7 =>
                simp only [h7] at h
                obtain ⟨pD, eD, rfl⟩ := timeREAdd_ok _ _ _ _ h1
                obtain ⟨pF, eF, rfl⟩ := timeREAdd_ok _ _ _ _ h2
                obtain ⟨_, _, rfl⟩ := timeREAdd_ok _ _ _ _ h3
                obtain ⟨_, _, rfl⟩ := timeREAdd_ok _ _ _ _ h4
                obtain ⟨_, _, rfl⟩ := timeREAdd_ok _ _ _ _ h5
                obtain ⟨_, _, rfl⟩ := timeREAdd_ok _ _ _ _ h6
                obtain ⟨_, _, rfl⟩ := timeREAdd_ok _ _ _ _ h7
                obtain ⟨_, _, rfl⟩ := timeREAdd_ok _ _ _ _ h
                have vD : timeREPattern (fun k => List.lookup k (timeREBase lt)) "%m/%d/%y" =
                    .ok "(?P<m>1[0-2]|0[1-9]|[1-9])/(?P<d>3[0-1]|[1-2]\\d|0[1-9]|[1-9]| [1-9])/(?P<y>\\d\\d)" := rfl
                rw [vD] at eD
                cases eD
                have vF : timeREPattern (fun k => List.lookup k (("D", "(?P<m>1[0-2]|0[1-9]|[1-9])/(?P<d>3[0-1]|[1-2]\\d|0[1-9]|[1-9]| [1-9])/(?P<y>\\d\\d)") :: timeREBase lt)) "%Y-%m-%d" =
                    .ok "(?P<Y>\\d\\d\\d\\d)-(?P<m>1[0-2]|0[1-9]|[1-9])-(?P<d>3[0-1]|[1-2]\\d|0[1-9]|[1-9]| [1-9])" := rfl
                rw [vF] at eF
                cases eF
                exact ⟨rfl, rfl⟩

/-- The translation of `format` before `TimeRE.pattern` looks at the flags, or `none` if a
directive is bad. -/
def strptimeTranslated (lt : LocaleTimeV) (format : String) : Option (List Char) :=
  match timeREMap lt with
  | .error _ => none
  | .ok m =>
    let s := quoteFormat (spaceFormat (escapeFormat format.toList))
    match replaceDirectives (fun k => List.lookup k m) s.length {} s with
    | .ok (t, _) => some t
    | .error _ => none

/-- Whether a translated format captures a year, in a group `_strptime` reads as one. -/
def hasYearGroup (t : List Char) : Bool :=
  !(findall t "(?P<Y>".toList).isEmpty || !(findall t "(?P<y>".toList).isEmpty ||
    !(findall t "(?P<G>".toList).isEmpty

/-- `TimeRE.pattern` calls a format one "without a year directive" only if it is: a format
whose translation captures a year does not raise that `ValueError`. -/
def StrptimeDayNeedsYear : Prop :=
  ∀ (lt : LocaleTimeV) (format : String) (t : List Char), strptimeTranslated lt format = some t →
    hasYearGroup t = true → strptimeCompile lt format ≠ .error (.valueError dayWithoutYearMsg)

/-- `LocaleTime` where `locale.ALT_DIGITS` is unavailable (`LC_alt_digits is None`), as far as
this format reads it. -/
def noAltDigitsLocale : LocaleTimeV where
  fWeekday := ["monday", "tuesday", "wednesday", "thursday", "friday", "saturday", "sunday"]
  aWeekday := ["mon", "tue", "wed", "thu", "fri", "sat", "sun"]
  fMonth := ["", "january", "february", "march", "april", "may", "june", "july", "august", "september", "october",
    "november", "december"]
  aMonth := ["", "jan", "feb", "mar", "apr", "may", "jun", "jul", "aug", "sep", "oct", "nov", "dec"]
  amPm := ["am", "pm"]
  timezone := [["utc", "gmt"], []]
  lcDateTime := "%a %b %d %H:%M:%S %Y"
  lcDate := "%m/%d/%y"
  lcTime := "%H:%M:%S"
  lcTimeAmpm := "%I:%M:%S %p"
  altDigits := none
  ambiguousTz := false

set_option maxRecDepth 100000 in
/-- `%d/%m/%Oy` captures the year in group `y`, and `TimeRE.pattern` still raises: `repl`
compares the directive with `Y`, `y` and `G` only, so `%Oy` does not set `year_in_format`. -/
theorem strptimeDayNeedsYear_refuted : ¬StrptimeDayNeedsYear := by
  intro h
  have ht : strptimeTranslated noAltDigitsLocale "%d/%m/%Oy" =
      some "(?P<d>3[0-1]|[1-2]\\d|0[1-9]|[1-9]| [1-9])/(?P<m>1[0-2]|0[1-9]|[1-9])/(?P<y>\\d\\d|\\d| \\d)".toList := by decide
  exact h _ _ _ ht (by decide) (by decide)

end PyLean.Datetime
