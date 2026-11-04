import PyLean.Datetime.DtProps
import PyLean.Datetime.Strftime
import PyLean.Datetime.Misc
import PyLean.Datetime.Strptime

/-!
POSIX seconds, packed-field accessors, subclass construction, `__format__`,
`tzinfo.__reduce__`, and the `_strptime` properties.
-/

namespace PyLean.Datetime

open PyLean

/-! ### POSIX seconds -/

/-- `datetime._mktime` and `local_to_seconds` compute the same seconds for every
local-time function. `fold` is a `datetime`'s, so 0 or 1. -/
def MktimeTwins : Prop :=
  ∀ (loc : Int → Py Int) (t fold : Int), (fold = 0 ∨ fold = 1) → mktimePy loc t fold = localToSecondsC loc t fold

theorem mktimeTwins_proven : MktimeTwins := by
  intro loc t fold hf
  rcases hf with rfl | rfl <;> rfl

/-- In a zone with a fixed offset, local seconds `t` are POSIX seconds `t - off`, for
either `fold`. -/
def MktimeFixedOffset : Prop :=
  ∀ (off t fold : Int), mktimePy (fun u => .ok (u + off)) t fold = .ok (t - off) ∧
    (fold = 0 ∨ fold = 1 → localToSecondsC (fun u => .ok (u + off)) t fold = .ok (t - off))

theorem mktimeFixedOffset_proven : MktimeFixedOffset := by
  intro off t fold
  have e : mktimePy (fun u => .ok (u + off)) t fold = .ok (t - off) := by
    have e1 : t + off - t = off := by omega
    have e2 : t - off + off = t := by omega
    simp [mktimePy, bind, Except.bind, pure, Except.pure, e1, e2]
    omega
  exact ⟨e, fun h => by rw [← mktimeTwins_proven _ t fold h]; exact e⟩

/-- `utc_to_seconds`: seconds since 0001-01-01 less a day, for a valid date; a year
out of range raises `ValueError`. -/
def UtcToSeconds : Prop :=
  ∀ y m d hh mi s : Int,
    (ValidDate y m d → utcToSecondsC y m d hh mi s = .ok (ymd2ord y m d * 86400 + hh * 3600 + mi * 60 + s)) ∧
    (¬(MINYEAR ≤ y ∧ y ≤ MAXYEAR) → (utcToSecondsC y m d hh mi s).raises "ValueError")

theorem utcToSeconds_proven : UtcToSeconds := by
  intro y m d hh mi s
  constructor
  · intro h
    have hp := validDate_pos _ _ _ h
    unfold utcToSecondsC
    rw [if_neg (by unfold MINYEAR MAXYEAR; omega), ymdToOrdC_eq y m d (by omega)]
    congr 1
    omega
  · intro h
    unfold utcToSecondsC
    rw [if_pos (by omega)]
    exact ⟨_, rfl, rfl⟩

/-! ### Packed fields -/

/-- `PyDateTime_GET_YEAR`, Include/datetime.h: the two big-endian bytes `data[0..1]`. -/
def getYear (data : List Nat) : Int := data.getD 0 0 * 256 + data.getD 1 0
/-- `PyDateTime_GET_MONTH`. -/
def getMonth (data : List Nat) : Int := data.getD 2 0
/-- `PyDateTime_GET_DAY`. -/
def getDay (data : List Nat) : Int := data.getD 3 0
/-- `PyDateTime_DATE_GET_HOUR` and the other fields of a `datetime`. -/
def dtGetHour (data : List Nat) : Int := data.getD 4 0
def dtGetMinute (data : List Nat) : Int := data.getD 5 0
def dtGetSecond (data : List Nat) : Int := data.getD 6 0
def dtGetUs (data : List Nat) : Int := (data.getD 7 0 * 65536 + data.getD 8 0 * 256 + data.getD 9 0 : Nat)
/-- `PyDateTime_TIME_GET_HOUR` and the other fields of a `time`. -/
def tmGetHour (data : List Nat) : Int := data.getD 0 0
def tmGetMinute (data : List Nat) : Int := data.getD 1 0
def tmGetSecond (data : List Nat) : Int := data.getD 2 0
def tmGetUs (data : List Nat) : Int := (data.getD 3 0 * 65536 + data.getD 4 0 * 256 + data.getD 5 0 : Nat)

/-- The C accessors `date_year`.. read the packed `data` bytes; for every valid object
they return the field the Python class keeps as an attribute. -/
def PackedAccessors : Prop :=
  (∀ (dt : DT), dt.Valid →
    getYear (dtData dt) = dt.y ∧ getMonth (dtData dt) = dt.m ∧ getDay (dtData dt) = dt.d ∧
    dtGetHour (dtData dt) = dt.h ∧ dtGetMinute (dtData dt) = dt.mi ∧ dtGetSecond (dtData dt) = dt.s ∧
    dtGetUs (dtData dt) = dt.us) ∧
  (∀ (t : TM), t.Valid →
    tmGetHour (timeData t) = t.h ∧ tmGetMinute (timeData t) = t.mi ∧ tmGetSecond (timeData t) = t.s ∧
    tmGetUs (timeData t) = t.us) ∧
  (∀ y m d : Int, ValidDate y m d →
    getYear (dateData y m d) = y ∧ getMonth (dateData y m d) = m ∧ getDay (dateData y m d) = d)

theorem packedAccessors_proven : PackedAccessors := by
  refine ⟨?_, ?_, ?_⟩
  · intro dt hv
    have p := validDate_pos _ _ _ hv.1
    obtain ⟨_, h1, h2, h3, h4, h5, h6, h7, h8, _⟩ := hv
    have e1 : getYear (dtData dt) = ((dt.y / 256).toNat : Int) * 256 + ((dt.y % 256).toNat : Int) := rfl
    have e2 : getMonth (dtData dt) = (dt.m.toNat : Int) := rfl
    have e3 : getDay (dtData dt) = (dt.d.toNat : Int) := rfl
    have e4 : dtGetHour (dtData dt) = (dt.h.toNat : Int) := rfl
    have e5 : dtGetMinute (dtData dt) = (dt.mi.toNat : Int) := rfl
    have e6 : dtGetSecond (dtData dt) = (dt.s.toNat : Int) := rfl
    have e7 : dtGetUs (dtData dt) = (((dt.us / 65536).toNat * 65536 + (dt.us / 256 % 256).toNat * 256 +
      (dt.us % 256).toNat : Nat) : Int) := rfl
    rw [e1, e2, e3, e4, e5, e6, e7]
    omega
  · intro t hv
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, _⟩ := hv
    have e4 : tmGetHour (timeData t) = (t.h.toNat : Int) := rfl
    have e5 : tmGetMinute (timeData t) = (t.mi.toNat : Int) := rfl
    have e6 : tmGetSecond (timeData t) = (t.s.toNat : Int) := rfl
    have e7 : tmGetUs (timeData t) = (((t.us / 65536).toNat * 65536 + (t.us / 256 % 256).toNat * 256 +
      (t.us % 256).toNat : Nat) : Int) := rfl
    rw [e4, e5, e6, e7]
    omega
  · intro y m d h
    have p := validDate_pos _ _ _ h
    have e1 : getYear (dateData y m d) = ((y / 256).toNat : Int) * 256 + ((y % 256).toNat : Int) := rfl
    have e2 : getMonth (dateData y m d) = (m.toNat : Int) := rfl
    have e3 : getDay (dateData y m d) = (d.toNat : Int) := rfl
    rw [e1, e2, e3]
    omega

/-! ### Subclass construction

The constructors that may call a subclass are in `SubclassCtor.lean`. -/

/-! ### `__format__` and `tzinfo.__reduce__` -/

/-- `format(x, '') == str(x)`, and `format(x, f) == x.strftime(f)` for nonempty `f`,
for `date` and `time`, in both twins. -/
def FormatViaStrftime : Prop :=
  ∀ (env : TzEnv) (y m d : Int) (t : TM) (s : String) (fmt : List Char) (gyear : Int) (norm : Bool),
    (fmt = [] →
      formatVia fmt (.ok s) (dateStrftimePy env y m d · gyear norm) = .ok (.inl s) ∧
      formatVia fmt (.ok s) (dateStrftimeC env y m d · gyear norm) = .ok (.inl s) ∧
      formatVia fmt (.ok s) (tmStrftimePy env t · norm) = .ok (.inl s) ∧
      formatVia fmt (.ok s) (tmStrftimeC env t · norm) = .ok (.inl s)) ∧
    (fmt ≠ [] →
      formatVia fmt (.ok s) (dateStrftimePy env y m d · gyear norm) = Sum.inr <$> dateStrftimePy env y m d fmt gyear norm ∧
      formatVia fmt (.ok s) (dateStrftimeC env y m d · gyear norm) = Sum.inr <$> dateStrftimeC env y m d fmt gyear norm ∧
      formatVia fmt (.ok s) (tmStrftimePy env t · norm) = Sum.inr <$> tmStrftimePy env t fmt norm ∧
      formatVia fmt (.ok s) (tmStrftimeC env t · norm) = Sum.inr <$> tmStrftimeC env t fmt norm)

theorem formatViaStrftime_proven : FormatViaStrftime := by
  intro env y m d t s fmt gyear norm
  constructor
  · intro h; subst h
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro h
    have e : fmt.isEmpty = false := by cases fmt <;> simp_all
    simp [formatVia, e]

/-- `tzinfo.__reduce__`: with no `__getinitargs__` the constructor gets no arguments; with
one, its result; the state follows; an exception of either propagates. -/
def TzinfoReduce : Prop :=
  ∀ {α σ : Type} (f : Unit → Py (List α)) (args : List α) (st : Py σ) (e : PyExc) (v : σ),
    tzinfoReduce (α := α) none st = (fun v => (([] : List α), v)) <$> st ∧
    (f () = .ok args → tzinfoReduce (some f) st = (fun v => (args, v)) <$> st) ∧
    (f () = .error e → tzinfoReduce (some f) (.ok v) = .error e)

theorem tzinfoReduce_proven : TzinfoReduce := by
  intro α σ f args st e v
  refine ⟨?_, ?_, ?_⟩
  · cases st <;> rfl
  · intro h
    simp only [tzinfoReduce, h]
    cases st <;> rfl
  · intro h
    simp only [tzinfoReduce, h]
    rfl

/-! ### `_sanitize_isoformat_str` -/

/-- `Py_UNICODE_IS_SURROGATE`. -/
def isSurrogate (c : Nat) : Bool := 0xD800 ≤ c && c ≤ 0xDFFF

/-- The search of `_sanitize_isoformat_str`, :5914-5966: reading index `len` gives NUL. -/
def surrogateSeparator (s : List Nat) : Nat :=
  let rec go : List Nat → Nat
    | [] => 0
    | pos :: rest =>
      if pos > s.length then 0
      else if isSurrogate (s.getD pos 0) then pos else go rest
  go [7, 8, 10]

/-- `_sanitize_isoformat_str`, :5914-5966, over code points; `none` is `NULL`. -/
def sanitizeIsoformatC (s : List Nat) : Option (List Nat) :=
  if s.length < 7 then none
  else
    let pos := surrogateSeparator s
    if pos = 0 then some s else some (s.set pos 84)

/-- A string with no surrogate at positions 7, 8, 10 comes back unchanged; a surrogate
there is replaced by `T` and the rest is untouched; short strings fail. -/
def SanitizeIsoformat : Prop :=
  ∀ s : List Nat,
    (s.length < 7 → sanitizeIsoformatC s = none) ∧
    (7 ≤ s.length → (∀ p, p = 7 ∨ p = 8 ∨ p = 10 → isSurrogate (s.getD p 0) = false) →
      sanitizeIsoformatC s = some s) ∧
    (7 < s.length → isSurrogate (s.getD 7 0) = true → sanitizeIsoformatC s = some (s.set 7 84))

theorem sanitizeIsoformat_proven : SanitizeIsoformat := by
  intro s
  refine ⟨?_, ?_, ?_⟩
  · intro h
    simp [sanitizeIsoformatC, h]
  · intro h hn
    have h7 := hn 7 (by simp)
    have h8 := hn 8 (by simp)
    have h10 := hn 10 (by simp)
    rw [List.getD_eq_getElem?_getD] at h7 h8 h10
    have e : surrogateSeparator s = 0 := by
      simp [surrogateSeparator, surrogateSeparator.go, h7, h8, h10]
    simp [sanitizeIsoformatC, e, show ¬ s.length < 7 by omega]
  · intro h hs
    rw [List.getD_eq_getElem?_getD] at hs
    have e : surrogateSeparator s = 7 := by
      simp [surrogateSeparator, surrogateSeparator.go, hs, show ¬ 7 > s.length by omega]
    simp [sanitizeIsoformatC, e, show ¬ s.length < 7 by omega]

/-! ### `_strptime` -/

/-- `_calc_julian_from_U_or_W`: the day of the year it returns falls on the requested
weekday (Monday is 0), for week numbers counted from Monday or from Sunday, and every
week number including 0. -/
def CalcJulianWeekday : Prop :=
  ∀ (year w dow : Int) (mon : Bool) (j : Int), calcJulianFromUorW year w dow mon = .ok j →
    (dateWeekdayC year 1 1 + j - 1) % 7 = dow % 7

theorem calcJulianWeekday_proven : CalcJulianWeekday := by
  intro year w dow mon j h
  unfold calcJulianFromUorW at h
  cases hd : checkDate year 1 1 with
  | error e => simp [hd, bind, Except.bind] at h
  | ok r =>
    simp only [hd, bind, Except.bind, pure, Except.pure] at h
    generalize dateWeekdayC year 1 1 = f at h ⊢
    cases mon <;> simp only [Bool.not_false, Bool.not_true, ite_true, ite_false, Bool.false_eq_true] at h <;>
      (split at h <;> (simp only [Except.ok.injEq] at h; omega))

/-- `insertByLen` keeps a list sorted, longest first. -/
theorem insertByLen_sorted (x : String) (l : List String)
    (h : l.Pairwise (fun a b => a.length ≥ b.length)) :
    (insertByLen x l).Pairwise (fun a b => a.length ≥ b.length) ∧ (insertByLen x l).Perm (x :: l) := by
  induction l with
  | nil => simp [insertByLen]
  | cons y ys ih =>
    unfold insertByLen
    by_cases hc : y.length ≥ x.length
    · simp only [hc, ite_true]
      obtain ⟨ih1, ih2⟩ := ih (List.pairwise_cons.mp h).2
      constructor
      · refine List.pairwise_cons.mpr ⟨?_, ih1⟩
        intro a ha
        rcases List.mem_cons.mp (ih2.mem_iff.mp ha) with rfl | ha'
        · exact hc
        · exact (List.pairwise_cons.mp h).1 a ha'
      · exact (List.Perm.cons y ih2).trans (List.Perm.swap x y ys)
    · simp only [hc, ite_false]
      constructor
      · refine List.pairwise_cons.mpr ⟨?_, h⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha'
        · omega
        · have := (List.pairwise_cons.mp h).1 a ha'
          omega
      · exact List.Perm.refl _

theorem sortByLen_aux (l acc : List String) (h : acc.Pairwise (fun a b => a.length ≥ b.length)) :
    (l.foldl (fun acc x => insertByLen x acc) acc).Pairwise (fun a b => a.length ≥ b.length) ∧
      (l.foldl (fun acc x => insertByLen x acc) acc).Perm (l ++ acc) := by
  induction l generalizing acc with
  | nil => simp [h]
  | cons x xs ih =>
    obtain ⟨h1, h2⟩ := insertByLen_sorted x acc h
    obtain ⟨i1, i2⟩ := ih _ h1
    refine ⟨i1, i2.trans ?_⟩
    exact (List.Perm.append_left xs h2).trans List.perm_middle

/-- `TimeRE.__seqToRE` sorts the alternatives longest first, and keeps all of them, so a
locale name that is a prefix of another cannot shadow it in the regex. -/
def SeqToRESorted : Prop :=
  ∀ xs : List String,
    (sortByLenDesc xs).Pairwise (fun a b => a.length ≥ b.length) ∧ (sortByLenDesc xs).Perm xs

theorem seqToRESorted_proven : SeqToRESorted := by
  intro xs
  obtain ⟨h1, h2⟩ := sortByLen_aux xs [] List.Pairwise.nil
  exact ⟨h1, by unfold sortByLenDesc; simpa using h2⟩

/-- `TimeRE.compile`: once the locale formats have been translated, a bad format only
ever produces `ValueError`, never the internal `KeyError`. -/
def StrptimeCompileErrors : Prop :=
  ∀ (lt : LocaleTimeV) (format : String) (m : List (String × String)), timeREMap lt = .ok m →
    (∃ p, strptimeCompile lt format = .ok p) ∨ (strptimeCompile lt format).raises "ValueError"

theorem strptimeCompileErrors_proven : StrptimeCompileErrors := by
  intro lt format m hm
  unfold strptimeCompile
  rw [hm]
  simp only
  cases timeREPattern (fun k => List.lookup k m) format with
  | ok p => exact Or.inl ⟨p, rfl⟩
  | error e =>
    cases e with
    | key bad =>
      refine Or.inr ⟨_, rfl, ?_⟩
      unfold badDirectiveError
      dsimp only
      split <;> rfl
    | value msg => exact Or.inr ⟨_, rfl, rfl⟩

theorem newDT_inv (dt r : DT) (h : newDT dt = .ok r) :
    r = dt ∧ checkDate dt.y dt.m dt.d = .ok (dt.y, dt.m, dt.d) ∧
      (∃ q, checkTime dt.h dt.mi dt.s dt.us = .ok q) ∧ checkFold dt.fold = .ok () := by
  unfold newDT at h
  cases hd : checkDate dt.y dt.m dt.d with
  | error e => simp [hd, bind, Except.bind] at h
  | ok a =>
    cases ht : checkTime dt.h dt.mi dt.s dt.us with
    | error e => simp [hd, ht, bind, Except.bind] at h
    | ok b =>
      cases hf : checkFold dt.fold with
      | error e => simp [hd, ht, hf, bind, Except.bind] at h
      | ok c =>
        simp [hd, ht, hf, bind, Except.bind, pure, Except.pure] at h
        have := (checkDate_inv _ _ _ _ hd).2
        subst this
        exact ⟨h.symm, rfl, ⟨b, rfl⟩, rfl⟩

/-- `date.strptime`, `time.strptime` and `datetime.strptime` read one parse: when the
`datetime` succeeds, the `date` is its date and the `time` its time and tzinfo. -/
def StrptimeMethods : Prop :=
  ∀ (lt : LocaleTimeV) (found : StrpFound) (dt : DT), strptimeDatetime lt found = .ok dt →
    strptimeDate lt found = .ok (dt.y, dt.m, dt.d) ∧ strptimeDatetimeTime lt found = .ok (dtTimetz dt)

theorem strptimeMethods_proven : StrptimeMethods := by
  intro lt found dt h
  unfold strptimeDatetime at h
  unfold strptimeDate strptimeDatetimeTime
  cases hc : strptimeCore lt found with
  | error e => simp [hc, bind, Except.bind] at h
  | ok r =>
    simp only [hc, bind, Except.bind] at h ⊢
    cases hg : r.gmtoff with
    | none =>
      simp only [hg] at h ⊢
      obtain ⟨e, h1, ⟨q, h2⟩, h3⟩ := newDT_inv _ _ h
      simp only at h1 h2 h3
      subst e
      refine ⟨h1, ?_⟩
      simp [newTM, h2, h3, dtTimetz, bind, Except.bind, pure, Except.pure]
    | some g =>
      simp only [hg] at h ⊢
      cases hz : parseTz r.tzname g r.gmtoffFraction with
      | error e => simp [hz] at h
      | ok tz =>
        simp only [hz] at h ⊢
        obtain ⟨e, h1, ⟨q, h2⟩, h3⟩ := newDT_inv _ _ h
        simp only at h1 h2 h3
        subst e
        refine ⟨h1, ?_⟩
        simp [newTM, h2, h3, dtTimetz, bind, Except.bind, pure, Except.pure]

end PyLean.Datetime
