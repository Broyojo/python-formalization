import PyLean.Datetime.ClsRows
import PyLean.Datetime.SubObjProps

/-!
Properties of the class-aware models of ClsRows.lean, CPython 3.15.2.
-/

namespace PyLean.Datetime
open PyLean

/-! ### Lemmas -/

theorem fitsCInt_iff (n : Int) : fitsCInt n ↔ (-2147483648 ≤ n ∧ n ≤ 2147483647) := by
  simp [fitsCInt]

theorem parseI_big (p : Int) (hp : ¬ fitsCInt p) :
    parseI (.int p) = .error (.overflowError "Python int too large to convert to C int") := by
  show asCInt p = _
  unfold asCInt
  exact if_neg hp

/-- A kept or given `int` field of `replace`. -/
def keepI (old : Int) : Option Arg → Int
  | some (.int n) => n
  | _ => old

theorem replArg_int (old : Int) (na : Option Arg) (hold : fitsCInt old)
    (h : ∀ a, na = some a → ∃ n, a = .int n ∧ fitsCInt n) :
    replKeep old na = .int (keepI old na) ∧ replConv old na = .ok (keepI old na) ∧ fitsCInt (keepI old na) := by
  cases na with
  | none => exact ⟨rfl, rfl, hold⟩
  | some a =>
    obtain ⟨n, rfl, hn⟩ := h a rfl
    refine ⟨rfl, ?_, hn⟩
    rw [fitsCInt_iff] at hn
    simp [replConv, parseI, pyIndex, asCInt, keepI, bind, Except.bind, hn]

theorem implC_tz_newDT (y m d h mi s us f : Int) (z : Option Tz) :
    datetimeDatetimeImplC y m d h mi s us (tzArgOf z) f = newDT ⟨y, m, d, h, mi, s, us, f, z⟩ := by
  unfold datetimeDatetimeImplC newDT
  cases checkDate y m d <;> cases checkTime h mi s us <;> cases checkFold f <;> cases z <;>
    simp [bind, Except.bind, checkTzinfoSubclassC, tzArgOf, pure, Except.pure]

theorem timeImplC_tz_newTM (h mi s us f : Int) (z : Option Tz) :
    datetimeTimeImplC h mi s us (tzArgOf z) f = newTM ⟨h, mi, s, us, f, z⟩ := by
  unfold datetimeTimeImplC newTM
  cases checkTime h mi s us <;> cases checkFold f <;> cases z <;>
    simp [bind, Except.bind, checkTzinfoSubclassC, tzArgOf, pure, Except.pure]

/-! ### `date.replace` -/

/-- `date.replace` in both twins for every receiver class (`date`, `datetime` calling
`date.replace`, or a subclass), every valid date and every combination of omitted fields and
C-int `int` arguments: the C method builds through `Py_TYPE(self)` as Python's
`type(self)(year, month, day)` does (the same result or the same exception, message included);
a subclass is called with exactly the kept or given fields, positionally, no keyword; and a
given field outside the C `int` range is `OverflowError` in C before any construction. -/
def DateReplaceCls : Prop :=
  (∀ (cls : DateClsC) (y m d : Int) (ny nm nd : Option Arg), ValidDate y m d →
    (∀ a, ny = some a ∨ nm = some a ∨ nd = some a → ∃ n, a = .int n ∧ fitsCInt n) →
    dateReplaceClsC cls y m d ny nm nd = dateReplaceClsPy cls y m d ny nm nd ∧
    (∀ call, dateReplaceClsC (.sub call) y m d ny nm nd =
      call [.int (keepI y ny), .int (keepI m nm), .int (keepI d nd)] none)) ∧
  (∀ (cls : DateClsC) (y m d n : Int) (nm nd : Option Arg), ¬ fitsCInt n →
    (dateReplaceClsC cls y m d (some (.int n)) nm nd).raises "OverflowError")

theorem dateReplaceCls_proven : DateReplaceCls := by
  refine ⟨fun cls y m d ny nm nd hv hargs => ?_, fun cls y m d n nm nd hn => ?_⟩
  · have hp := validDate_pos _ _ _ hv
    have hy : fitsCInt y := by unfold fitsCInt; omega
    have hm : fitsCInt m := by unfold fitsCInt; omega
    have hd : fitsCInt d := by unfold fitsCInt; unfold ValidDate at hv; omega
    obtain ⟨ky, cy, fy⟩ := replArg_int y ny hy (fun a h => hargs a (Or.inl h))
    obtain ⟨km, cm, fm⟩ := replArg_int m nm hm (fun a h => hargs a (Or.inr (Or.inl h)))
    obtain ⟨kd, cd, fd⟩ := replArg_int d nd hd (fun a h => hargs a (Or.inr (Or.inr h)))
    have hc : ∀ cls, dateReplaceClsC cls y m d ny nm nd =
        newDateSubclassExC (keepI y ny) (keepI m nm) (keepI d nd) cls := by
      intro cls
      simp only [dateReplaceClsC, cy, cm, cd, bind, Except.bind]
    refine ⟨?_, fun call => by rw [hc]; rfl⟩
    rw [hc, (dateSubclassCtor_proven _ _ _ fy fm fd).1 cls]
    cases cls <;> simp only [dateClsCallPy, dateReplaceClsPy, ky, km, kd]
  · have : replConv y (some (.int n)) = .error (.overflowError "Python int too large to convert to C int") := by
      rw [fitsCInt_iff] at hn
      simp [replConv, parseI, pyIndex, asCInt, hn, bind, Except.bind]
    exact ⟨.overflowError "Python int too large to convert to C int", by simp only [dateReplaceClsC, this, bind, Except.bind], rfl⟩

/-! ### `time.replace`, `datetime.replace` -/

/-- `time.replace` in C for every receiver type: for `time` itself it is `tmReplaceC` (the
field checks of `time()`, pinned against Python by `TimeReplaceInt`); for a subclass, with
every field in the C `int` range, the class is called with the kept or given fields and
tzinfo positionally and `fold` as a keyword only when it is nonzero (`call_subclass_fold`),
and its result is returned without a check; a field outside the C `int` range is
`OverflowError` before any call. -/
def TimeReplaceCls : Prop :=
  ∀ (t : TM) (h mi s us fold : Option Int) (tz : Option (Option Tz)),
    tmReplaceClsC .base t h mi s us fold tz = tmReplaceC t h mi s us fold tz ∧
    (∀ call : SubCall TM, fitsCInt (h.getD t.h) → fitsCInt (mi.getD t.mi) → fitsCInt (s.getD t.s) →
      fitsCInt (us.getD t.us) → fitsCInt (fold.getD t.fold) →
      tmReplaceClsC (.sub call) t h mi s us fold tz =
        call [.int (h.getD t.h), .int (mi.getD t.mi), .int (s.getD t.s), .int (us.getD t.us), tzArgOf (tz.getD t.tz)]
          (if fold.getD t.fold ≠ 0 then some (fold.getD t.fold) else none)) ∧
    (∀ cls : ClsC TM, ¬(fitsCInt (h.getD t.h) ∧ fitsCInt (mi.getD t.mi) ∧ fitsCInt (s.getD t.s) ∧
      fitsCInt (us.getD t.us) ∧ fitsCInt (fold.getD t.fold)) →
      (tmReplaceClsC cls t h mi s us fold tz).raises "OverflowError")

theorem timeReplaceCls_proven : TimeReplaceCls := by
  intro t h mi s us fold tz
  refine ⟨?_, fun call h1 h2 h3 h4 h5 => ?_, fun cls hn => ?_⟩
  · unfold tmReplaceClsC tmReplaceC
    split
    · rfl
    · simp only [newTimeSubclassFoldExC, timeImplC_tz_newTM, tmReplace]
  · unfold tmReplaceClsC
    rw [if_neg (by simp [h1, h2, h3, h4, h5])]
    rfl
  · unfold tmReplaceClsC
    rw [if_pos hn]
    exact ⟨_, rfl, rfl⟩

/-- `datetime.replace` in C for every receiver type: for `datetime` it is `dtReplaceC`
(pinned against Python by `DatetimeReplaceInt`); for a subclass, with every field in the C
`int` range, the class is called with the eight fields positionally and `fold` as a keyword
only when nonzero; a field outside the range is `OverflowError` before any call. -/
def DatetimeReplaceCls : Prop :=
  ∀ (dt : DT) (y m d h mi s us fold : Option Int) (tz : Option (Option Tz)),
    dtReplaceClsC .base dt y m d h mi s us fold tz = dtReplaceC dt y m d h mi s us fold tz ∧
    (∀ call : SubCall DT, fitsCInt (y.getD dt.y) → fitsCInt (m.getD dt.m) → fitsCInt (d.getD dt.d) →
      fitsCInt (h.getD dt.h) → fitsCInt (mi.getD dt.mi) → fitsCInt (s.getD dt.s) →
      fitsCInt (us.getD dt.us) → fitsCInt (fold.getD dt.fold) →
      dtReplaceClsC (.sub call) dt y m d h mi s us fold tz =
        call [.int (y.getD dt.y), .int (m.getD dt.m), .int (d.getD dt.d), .int (h.getD dt.h), .int (mi.getD dt.mi),
          .int (s.getD dt.s), .int (us.getD dt.us), tzArgOf (tz.getD dt.tz)]
          (if fold.getD dt.fold ≠ 0 then some (fold.getD dt.fold) else none)) ∧
    (∀ cls : ClsC DT, ¬(fitsCInt (y.getD dt.y) ∧ fitsCInt (m.getD dt.m) ∧ fitsCInt (d.getD dt.d) ∧
      fitsCInt (h.getD dt.h) ∧ fitsCInt (mi.getD dt.mi) ∧ fitsCInt (s.getD dt.s) ∧
      fitsCInt (us.getD dt.us) ∧ fitsCInt (fold.getD dt.fold)) →
      (dtReplaceClsC cls dt y m d h mi s us fold tz).raises "OverflowError")

theorem datetimeReplaceCls_proven : DatetimeReplaceCls := by
  intro dt y m d h mi s us fold tz
  refine ⟨?_, fun call h0 h1 h2 h3 h4 h5 h6 h7 => ?_, fun cls hn => ?_⟩
  · unfold dtReplaceClsC dtReplaceC
    split
    · rfl
    · simp only [newDatetimeSubclassFoldExC, implC_tz_newDT, dtReplace]
  · unfold dtReplaceClsC
    rw [if_neg (by simp [h0, h1, h2, h3, h4, h5, h6, h7])]
    rfl
  · unfold dtReplaceClsC
    rw [if_pos hn]
    exact ⟨_, rfl, rfl⟩

/-! ### `combine` -/

/-- `datetime.combine` in C for every class it is called on: the argument checks come first
(the `date` then the `time` `TypeError`); for `datetime` the result is `dtCombineArgC`
(pinned against Python by `CombineArgs`); a subclass is called with the date's and time's
fields and the tzinfo (the time's when omitted) positionally, `fold` as a keyword only when
the time's fold is set. -/
def CombineCls : Prop :=
  (∀ (d : DateObj) (t : TimeObj) (tz : TzParam), dtCombineClsC .base d t tz = dtCombineArgC d t tz) ∧
  (∀ (call : SubCall DT) (y m dd : Int) (t : TM) (tz : TzParam),
    dtCombineClsC (.sub call) (.date y m dd) (.time t) tz =
      call [.int y, .int m, .int dd, .int t.h, .int t.mi, .int t.s, .int t.us, tzParamC t.tz tz]
        (if t.fold ≠ 0 then some t.fold else none)) ∧
  (∀ (cls : ClsC DT) (t : TimeObj) (tz : TzParam), (dtCombineClsC cls .other t tz).raises "TypeError") ∧
  (∀ (cls : ClsC DT) (y m dd : Int) (tz : TzParam), (dtCombineClsC cls (.date y m dd) .other tz).raises "TypeError")

theorem combineCls_proven : CombineCls := by
  refine ⟨fun d t tz => ?_, fun call y m dd t tz => rfl, fun cls t tz => ⟨_, rfl, rfl⟩,
    fun cls y m dd tz => ⟨_, rfl, rfl⟩⟩
  cases d <;> cases t <;> rfl

/-! ### `strptime` -/

/-- `time.strptime` in both twins, for every class: the C method passes its class to
`_strptime_datetime_time` as Python's does; for `time` the result is `strptimeDatetimeTime`'s;
a subclass is called with the parsed hour, minute, second and fraction, and the parsed
`timezone` as a fifth positional argument only when there was an offset; a parse error or an
invalid offset propagates before any call. -/
def TimeStrptimeCls : Prop :=
  ∀ (lt : LocaleTimeV) (found : StrpFound),
    (∀ cls, timeStrptimeImplC cls lt found = timeStrptimePy cls lt found) ∧
    timeStrptimeImplC .base lt found = strptimeDatetimeTime lt found ∧
    (∀ call r, strptimeCore lt found = .ok r → r.gmtoff = none →
      timeStrptimeImplC (.sub call) lt found = call [.int r.hour, .int r.minute, .int r.second, .int r.fraction] none) ∧
    (∀ call r g z, strptimeCore lt found = .ok r → r.gmtoff = some g → parseTz r.tzname g r.gmtoffFraction = .ok z →
      timeStrptimeImplC (.sub call) lt found =
        call [.int r.hour, .int r.minute, .int r.second, .int r.fraction, .tz z] none) ∧
    (∀ cls e, strptimeCore lt found = .error e → timeStrptimeImplC cls lt found = .error e) ∧
    (∀ cls r g e, strptimeCore lt found = .ok r → r.gmtoff = some g → parseTz r.tzname g r.gmtoffFraction = .error e →
      timeStrptimeImplC cls lt found = .error e)

theorem timeStrptimeCls_proven : TimeStrptimeCls := by
  intro lt found
  refine ⟨fun _ => rfl, ?_, fun call r h1 h2 => ?_, fun call r g z h1 h2 h3 => ?_, fun cls e h => ?_,
    fun cls r g e h1 h2 h3 => ?_⟩
  · unfold timeStrptimeImplC strptimeTimeCls strptimeDatetimeTime
    cases strptimeCore lt found with
    | error e => rfl
    | ok r =>
      simp only [bind, Except.bind, pure, Except.pure]
      cases r.gmtoff with
      | none => rfl
      | some g =>
        simp only [Functor.map, Except.map]
        cases parseTz r.tzname g r.gmtoffFraction <;> rfl
  · simp [timeStrptimeImplC, strptimeTimeCls, h1, h2, bind, Except.bind, pure, Except.pure]
  · simp [timeStrptimeImplC, strptimeTimeCls, h1, h2, h3, bind, Except.bind, pure, Except.pure, Functor.map,
      Except.map]
  · simp [timeStrptimeImplC, strptimeTimeCls, h, bind, Except.bind]
  · simp [timeStrptimeImplC, strptimeTimeCls, h1, h2, h3, bind, Except.bind, Functor.map, Except.map]

/-- `datetime.strptime` in both twins, for every class: as `TimeStrptimeCls`, with the parsed
year, month, day, hour, minute, second and fraction. -/
def DatetimeStrptimeCls : Prop :=
  ∀ (lt : LocaleTimeV) (found : StrpFound),
    (∀ cls, datetimeStrptimeImplC cls lt found = datetimeStrptimePy cls lt found) ∧
    datetimeStrptimeImplC .base lt found = strptimeDatetime lt found ∧
    (∀ call r, strptimeCore lt found = .ok r → r.gmtoff = none →
      datetimeStrptimeImplC (.sub call) lt found =
        call [.int r.year, .int r.month, .int r.day, .int r.hour, .int r.minute, .int r.second, .int r.fraction] none) ∧
    (∀ call r g z, strptimeCore lt found = .ok r → r.gmtoff = some g → parseTz r.tzname g r.gmtoffFraction = .ok z →
      datetimeStrptimeImplC (.sub call) lt found =
        call [.int r.year, .int r.month, .int r.day, .int r.hour, .int r.minute, .int r.second, .int r.fraction,
          .tz z] none) ∧
    (∀ cls e, strptimeCore lt found = .error e → datetimeStrptimeImplC cls lt found = .error e) ∧
    (∀ cls r g e, strptimeCore lt found = .ok r → r.gmtoff = some g → parseTz r.tzname g r.gmtoffFraction = .error e →
      datetimeStrptimeImplC cls lt found = .error e)

theorem datetimeStrptimeCls_proven : DatetimeStrptimeCls := by
  intro lt found
  refine ⟨fun _ => rfl, ?_, fun call r h1 h2 => ?_, fun call r g z h1 h2 h3 => ?_, fun cls e h => ?_,
    fun cls r g e h1 h2 h3 => ?_⟩
  · unfold datetimeStrptimeImplC strptimeDatetimeCls strptimeDatetime
    cases strptimeCore lt found with
    | error e => rfl
    | ok r =>
      simp only [bind, Except.bind, pure, Except.pure]
      cases r.gmtoff with
      | none => rfl
      | some g =>
        simp only [Functor.map, Except.map]
        cases parseTz r.tzname g r.gmtoffFraction <;> rfl
  · simp [datetimeStrptimeImplC, strptimeDatetimeCls, h1, h2, bind, Except.bind, pure, Except.pure]
  · simp [datetimeStrptimeImplC, strptimeDatetimeCls, h1, h2, h3, bind, Except.bind, pure, Except.pure, Functor.map,
      Except.map]
  · simp [datetimeStrptimeImplC, strptimeDatetimeCls, h, bind, Except.bind]
  · simp [datetimeStrptimeImplC, strptimeDatetimeCls, h1, h2, h3, bind, Except.bind, Functor.map, Except.map]

/-! ### `fromisoformat` -/

theorem timeFromIsoK_bind {α : Type} (s : List Char) (k : Int × Int × Int × Int × Option Int → Py α) :
    timeFromIsoK s k = timeFromIsoK s pure >>= k := by
  simp only [timeFromIsoK, bind, Except.bind, pure, Except.pure]
  repeat' split
  all_goals first | rfl | simp_all

theorem datetimeFromIsoK_bind {α : Type} (s : List Char)
    (k : Int × Int × Int × Int × Int × Int × Int × Option Int → Py α) :
    datetimeFromIsoK s k = datetimeFromIsoK s pure >>= k := by
  simp only [datetimeFromIsoK, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  repeat' split
  all_goals (try rfl)
  all_goals (try (simp_all only [Except.error.injEq, reduceCtorEq]; done))
  all_goals (try (rename_i h; cases h; rfl))

theorem timeFromIsoClsC_base (s : List Char) : timeFromIsoClsC .base s = timeFromIsoC s := rfl

theorem datetimeFromIsoK_base (s : List Char) : datetimeFromIsoK s dtIsoBaseTail = datetimeFromIsoC s := rfl

/-- `time.fromisoformat` in C for every class: for `time` it is `timeFromIsoC` (pinned against
Python by the fromisoformat entries); the parse runs first and its error (an invalid string,
the hour-24 rule, an offset out of range) is the result for every class, before any call; on
success `time` checks the values and a subclass is called with the hour, minute, second,
microsecond and tzinfo (`None`, `timezone.utc` or a new `timezone`) positionally, its result
returned unchecked. -/
def TimeFromIsoCls : Prop :=
  ∀ s : List Char,
    timeFromIsoClsC .base s = timeFromIsoC s ∧
    (∀ e, timeFromIsoK s pure = .error e → ∀ cls, timeFromIsoClsC cls s = .error e) ∧
    (∀ p, timeFromIsoK s pure = .ok p →
      timeFromIsoClsC .base s = tmIsoBaseTail p ∧ ∀ call, timeFromIsoClsC (.sub call) s = call (tmIsoArgs p) none)

theorem timeFromIsoCls_proven : TimeFromIsoCls := by
  intro s
  refine ⟨rfl, fun e he cls => ?_, fun p hp => ⟨?_, fun call => ?_⟩⟩
  · unfold timeFromIsoClsC
    rw [timeFromIsoK_bind, he]
    rfl
  · unfold timeFromIsoClsC
    rw [timeFromIsoK_bind, hp]
    rfl
  · unfold timeFromIsoClsC
    rw [timeFromIsoK_bind, hp]
    rfl

/-! ### `_sanitize_isoformat_str` -/

/-- `_sanitize_isoformat_str` on every path: a string shorter than 7 is `NULL`; the first of
the positions 7, 8, 10 (reading index `len` as the NUL terminator and stopping at a position
past it) that holds a surrogate is replaced by `T` and nothing else changes; with no surrogate
at those positions the string comes back unchanged. -/
def SanitizeIsoformatFull : Prop :=
  ∀ s : List Nat,
    (s.length < 7 → sanitizeIsoformatC s = none) ∧
    (7 ≤ s.length → (∀ p, p = 7 ∨ p = 8 ∨ p = 10 → isSurrogate (s.getD p 0) = false) →
      sanitizeIsoformatC s = some s) ∧
    (7 < s.length → isSurrogate (s.getD 7 0) = true → sanitizeIsoformatC s = some (s.set 7 84)) ∧
    (8 < s.length → isSurrogate (s.getD 7 0) = false → isSurrogate (s.getD 8 0) = true →
      sanitizeIsoformatC s = some (s.set 8 84)) ∧
    (10 < s.length → isSurrogate (s.getD 7 0) = false → isSurrogate (s.getD 8 0) = false →
      isSurrogate (s.getD 10 0) = true → sanitizeIsoformatC s = some (s.set 10 84))

theorem sanitizeIsoformatFull_proven : SanitizeIsoformatFull := by
  intro s
  obtain ⟨h1, h2, h3⟩ := sanitizeIsoformat_proven s
  refine ⟨h1, h2, h3, fun hl h7 h8 => ?_, fun hl h7 h8 h10 => ?_⟩
  · rw [List.getD_eq_getElem?_getD] at h7 h8
    have e : surrogateSeparator s = 8 := by
      simp [surrogateSeparator, surrogateSeparator.go, h7, h8, show ¬ 7 > s.length by omega,
        show ¬ 8 > s.length by omega]
    simp [sanitizeIsoformatC, e, show ¬ s.length < 7 by omega]
  · rw [List.getD_eq_getElem?_getD] at h7 h8 h10
    have e : surrogateSeparator s = 10 := by
      simp [surrogateSeparator, surrogateSeparator.go, h7, h8, h10, show ¬ 7 > s.length by omega,
        show ¬ 8 > s.length by omega, show ¬ 10 > s.length by omega]
    simp [sanitizeIsoformatC, e, show ¬ s.length < 7 by omega]

/-! ### `datetime.fromisoformat` -/

theorem map_ofNat_toNat (s : List Char) : (s.map Char.toNat).map Char.ofNat = s := by
  induction s with
  | nil => rfl
  | cons c t ih => simp [ih, Char.ofNat_toNat]

theorem noSurrogate_getD (l : List Nat) (h : l.any isSurrogate = false) (p : Nat) :
    isSurrogate (l.getD p 0) = false := by
  rw [List.getD_eq_getElem?_getD]
  cases hp : l[p]? with
  | none => rfl
  | some c =>
    have hm : c ∈ l := List.mem_of_getElem? hp
    simp only [List.any_eq_false] at h
    simpa using h c hm

/-- `datetime.fromisoformat` in C for every class, on the code points of any `str`: a string
without surrogates is `datetimeFromIsoC` for `datetime`; a surrogate at the separator position
`_sanitize_isoformat_str` picks behaves as `T` there; a surrogate left after sanitizing is
`ValueError` (the `UnicodeEncodeError` replaced); the parse's error is the result for every
class; on success `datetime` checks the values and a subclass is called with the eight values
positionally and no `fold` keyword. -/
def DatetimeFromIsoCls : Prop :=
  (∀ s : List Char, (s.map Char.toNat).any isSurrogate = false →
      datetimeFromIsoClsC .base (s.map Char.toNat) = datetimeFromIsoC s) ∧
  (∀ (cls : ClsC DateTimeV) (cps : List Nat) (q : Nat), (q = 7 ∨ q = 8 ∨ q = 10) → q < cps.length →
    sanitizeIsoformatC cps = some (cps.set q 84) → ((cps.set q 84).any isSurrogate = false) →
    datetimeFromIsoClsC cls cps = datetimeFromIsoClsC cls (cps.set q 84)) ∧
  (∀ (cls : ClsC DateTimeV) (cps clean : List Nat), sanitizeIsoformatC cps = some clean → clean.any isSurrogate = true →
    (datetimeFromIsoClsC cls cps).raises "ValueError") ∧
  (∀ (cps clean : List Nat), sanitizeIsoformatC cps = some clean → clean.any isSurrogate = false →
    (∀ e, datetimeFromIsoK (clean.map Char.ofNat) pure = .error e → ∀ cls, datetimeFromIsoClsC cls cps = .error e) ∧
    (∀ p, datetimeFromIsoK (clean.map Char.ofNat) pure = .ok p →
      datetimeFromIsoClsC .base cps = dtIsoBaseTail p ∧
      ∀ call, datetimeFromIsoClsC (.sub call) cps = callSubclassFoldC call 0 (dtIsoArgs p)))

theorem datetimeFromIsoCls_proven : DatetimeFromIsoCls := by
  refine ⟨fun s ha => ?_, fun cls cps q hq hl hs hn => ?_, fun cls cps clean hs ha => ?_, fun cps clean hs ha => ?_⟩
  · unfold datetimeFromIsoClsC
    by_cases hl : (s.map Char.toNat).length < 7
    · rw [(sanitizeIsoformat_proven _).1 hl]
      have : s.length < 7 := by simpa using hl
      simp only [datetimeFromIsoC, this, ↓reduceIte]
      rfl
    · rw [(sanitizeIsoformat_proven _).2.1 (by omega) (fun p _ => noSurrogate_getD _ ha p)]
      simp only [ha, Bool.false_eq_true, ↓reduceIte, map_ofNat_toNat]
      rfl
  · have hf : sanitizeIsoformatC (cps.set q 84) = some (cps.set q 84) :=
      (sanitizeIsoformat_proven _).2.1 (by simp; omega) (fun p _ => noSurrogate_getD _ hn p)
    simp only [datetimeFromIsoClsC, hs, hf]
  · simp only [datetimeFromIsoClsC, hs, ha, ↓reduceIte]
    exact ⟨_, rfl, rfl⟩
  · refine ⟨fun e he cls => ?_, fun p hp => ⟨?_, fun call => ?_⟩⟩
    · simp only [datetimeFromIsoClsC, hs, ha, Bool.false_eq_true, ↓reduceIte]
      rw [datetimeFromIsoK_bind, he]
      rfl
    · simp only [datetimeFromIsoClsC, hs, ha, Bool.false_eq_true, ↓reduceIte]
      rw [datetimeFromIsoK_bind, hp]
      rfl
    · simp only [datetimeFromIsoClsC, hs, ha, Bool.false_eq_true, ↓reduceIte]
      rw [datetimeFromIsoK_bind, hp]
      rfl

/-! ### `_find_isoformat_datetime_separator` -/

theorem utf8_ascii (s : List Char) (h : ∀ c ∈ s, c.toNat < 128) : utf8 s = s.map Char.toNat := by
  induction s with
  | nil => rfl
  | cons c t ih =>
    have hc := h c (by simp)
    simp only [utf8, List.flatMap_cons, List.map_cons] at ih ⊢
    rw [ih (fun x hx => h x (by simp [hx]))]
    simp [utf8Char, hc]

theorem byteAt_map (s : List Char) (i : Nat) : byteAt (s.map Char.toNat) i = (charAt s i).toNat := by
  unfold byteAt charAt
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases s[i]? <;> rfl

theorem isDigit_toNat (c : Char) : isDigitC c.toNat = isAsciiDigit c := by
  unfold isDigitC isAsciiDigit
  simp only [Char.le_def]
  rfl

theorem takeWhile_digitsC (s : List Char) :
    ((s.map Char.toNat).takeWhile isDigitC).length = (s.takeWhile isAsciiDigit).length := by
  induction s with
  | nil => rfl
  | cons c t ih =>
    simp only [List.map_cons, List.takeWhile_cons, isDigit_toNat]
    split <;> simp [ih]

theorem charEq (a b : Char) : (a.toNat = b.toNat) ↔ a = b := by
  constructor
  · intro h; exact Char.ext (UInt32.toNat_inj.mp h)
  · intro h; rw [h]

/-- Python's separator or its `ValueError`, as C reports them (`-1` for the error). -/
def sepToC : Py Nat → Int
  | .ok n => n
  | .error _ => -1

theorem sepToC_ok (n : Nat) : sepToC (.ok n) = (n : Int) := rfl
theorem sepToC_err (e : PyExc) : sepToC (.error e) = -1 := rfl

/-- C `_find_isoformat_datetime_separator` (on the UTF-8 bytes) and Python's (on the code
points) agree on every ASCII string of at least 7 characters, on every branch: the same
separator index, and C's `-1` exactly where Python raises `ValueError("Invalid ISO string")`. -/
def FindSepTwins : Prop :=
  ∀ s : List Char, (∀ c ∈ s, c.toNat < 128) → 7 ≤ s.length →
    findSepC (utf8 s) = sepToC (findSepPy s) ∧
    (∀ e, findSepPy s = .error e → e = .valueError "Invalid ISO string")

theorem findSepTwins_proven : FindSepTwins := by
  intro s hs hl
  rw [utf8_ascii s hs]
  have hlen : (s.map Char.toNat).length = s.length := List.length_map ..
  have hidx : (List.takeWhile isDigitC (List.take (s.length - 7) (List.drop 7 (List.map Char.toNat s)))).length =
      ((s.drop 7).takeWhile isAsciiDigit).length := by
    rw [List.take_of_length_le (by simp)]
    have : List.drop 7 (List.map Char.toNat s) = List.map Char.toNat (List.drop 7 s) := by simp
    rw [this, takeWhile_digitsC]
  have e45 : ∀ c : Char, (c.toNat = 45) ↔ c = '-' := fun c => charEq c '-'
  have e87 : ∀ c : Char, (c.toNat = 87) ↔ c = 'W' := fun c => charEq c 'W'
  constructor
  · unfold findSepC findSepPy
    simp only [hlen, byteAt_map, isDigit_toNat, e45, e87, hidx, apply_ite sepToC, sepToC_ok, sepToC_err]
    rfl
  · intro e
    unfold findSepPy
    simp only []
    repeat' split
    all_goals intro he
    all_goals first | exact (Except.error.inj he).symm | exact absurd he (by simp)

/-! ### `__reduce__`, `__reduce_ex__` -/

/-- `date.__reduce__` in both twins: `(type(self), (bytes,))` with the receiver's own type for
every class (a subclass pickles as itself) and the four state bytes. -/
def DateReduceCls : Prop :=
  ∀ (ty : Nat) (y m d : Int), dateReduceClsC ty y m d = dateReduceClsPy ty y m d ∧
    (dateReduceClsC ty y m d).1 = ty ∧ (dateReduceClsC ty y m d).2 = dateData y m d

theorem dateReduceCls_proven : DateReduceCls := fun _ _ _ _ => ⟨rfl, rfl, rfl⟩

/-- `time.__reduce_ex__(proto)` and `__reduce__()` in C for every receiver type: the protocol
goes through the clinic `int` converter first (`PyLong_AsInt`: an object without `__index__`
is `TypeError`, an int outside the C `int` range `OverflowError`), then the result is
`(type(self), state)` with the receiver's own type; for every protocol in the C `int` range it
is Python's `(self.__class__, self._getstate(protocol))`, and `__reduce__` is the state at
protocol 2 in both twins. -/
def TimeReduceExCls : Prop :=
  ∀ (ty : Nat) (t : TM), t.Valid →
    (∀ p : Int, fitsCInt p → tmReduceExClsC ty t (.int p) = .ok (tmReduceExClsPy ty t p)) ∧
    (∀ p : Int, ¬ fitsCInt p → (tmReduceExClsC ty t (.int p)).raises "OverflowError") ∧
    (∀ a : Arg, (∀ r, pyIndex a ≠ .ok r) → (tmReduceExClsC ty t a).isOk = false) ∧
    tmReduceClsC ty t = tmReduceExClsPy ty t 2

theorem timeReduceExCls_proven : TimeReduceExCls := by
  intro ty t hv
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun a ha => ?_, ?_⟩
  · rw [fitsCInt_iff] at hp
    simp [tmReduceExClsC, tmReduceExClsPy, parseI, pyIndex, asCInt, hp, bind, Except.bind, pure, Except.pure,
      tmReduceExC, tmReduceExPy, tmGetstate_twin t p hv]
  · refine ⟨.overflowError "Python int too large to convert to C int", ?_, rfl⟩
    unfold tmReduceExClsC
    rw [parseI_big p hp]
    rfl
  · unfold tmReduceExClsC parseI
    cases h : pyIndex a with
    | error e => rfl
    | ok r => exact absurd h (ha r)
  · simp [tmReduceClsC, tmReduceExClsPy, tmReduceC, tmReduceExPy, tmGetstate_twin t 2 hv]

/-- `datetime.__reduce_ex__(proto)` and `__reduce__()` in C for every receiver type, as
`TimeReduceExCls`. -/
def DatetimeReduceExCls : Prop :=
  ∀ (ty : Nat) (dt : DT), dt.Valid →
    (∀ p : Int, fitsCInt p → dtReduceExClsC ty dt (.int p) = .ok (dtReduceExClsPy ty dt p)) ∧
    (∀ p : Int, ¬ fitsCInt p → (dtReduceExClsC ty dt (.int p)).raises "OverflowError") ∧
    (∀ a : Arg, (∀ r, pyIndex a ≠ .ok r) → (dtReduceExClsC ty dt a).isOk = false) ∧
    dtReduceClsC ty dt = dtReduceExClsPy ty dt 2

theorem datetimeReduceExCls_proven : DatetimeReduceExCls := by
  intro ty dt hv
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun a ha => ?_, ?_⟩
  · rw [fitsCInt_iff] at hp
    simp [dtReduceExClsC, dtReduceExClsPy, parseI, pyIndex, asCInt, hp, bind, Except.bind, pure, Except.pure,
      dtReduceExC, dtReduceExPy, dtGetstate_twin dt p hv]
  · refine ⟨.overflowError "Python int too large to convert to C int", ?_, rfl⟩
    unfold dtReduceExClsC
    rw [parseI_big p hp]
    rfl
  · unfold dtReduceExClsC parseI
    cases h : pyIndex a with
    | error e => rfl
    | ok r => exact absurd h (ha r)
  · simp [dtReduceClsC, dtReduceExClsPy, dtReduceC, dtReduceExPy, dtGetstate_twin dt 2 hv]

/-- The broad twin: `time.__reduce_ex__(p)` agrees between C and Python for every valid time and
every int protocol `p`. -/
def TimeReduceExTwinsAllInt : Prop :=
  ∀ (ty : Nat) (t : TM) (p : Int), t.Valid → tmReduceExClsC ty t (.int p) = .ok (tmReduceExClsPy ty t p)

/-- `time(1).__reduce_ex__(2**31)`: C's `int` converter raises `OverflowError`, Python returns. -/
theorem timeReduceExTwinsAllInt_refuted : ¬ TimeReduceExTwinsAllInt := by
  intro h
  have := h 0 ⟨1, 0, 0, 0, 0, none⟩ (2 ^ 31)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, Or.inl rfl, trivial⟩
  revert this
  decide

/-- The broad twin for `datetime.__reduce_ex__`. -/
def DatetimeReduceExTwinsAllInt : Prop :=
  ∀ (ty : Nat) (dt : DT) (p : Int), dt.Valid → dtReduceExClsC ty dt (.int p) = .ok (dtReduceExClsPy ty dt p)

/-- `datetime(2000, 1, 1).__reduce_ex__(2**31)`: C `OverflowError`, Python returns. -/
theorem datetimeReduceExTwinsAllInt_refuted : ¬ DatetimeReduceExTwinsAllInt := by
  intro h
  have := h 0 ⟨2000, 1, 1, 0, 0, 0, 0, 0, none⟩ (2 ^ 31)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, Or.inl rfl,
      trivial⟩
  revert this
  decide

/-- `tzinfo.__reduce__` in both twins for every receiver type: the C result is `tzinfoReduceC`'s
arguments and state (pinned by `TzinfoReduceBody`) with `type(self)` first, Python's the same
with `tzinfoReducePy`'s; where those agree (the `__getinitargs__` truth difference is refuted on
record) the triples agree, and the first element is always the receiver's type. -/
def TzinfoReduceCls : Prop :=
  ∀ {α σ : Type} (ty : Nat) (attr : Py (Option (InitArgsObj α))) (state : Py σ),
    tzinfoReduceClsC ty attr state = (fun r => (ty, r.1, r.2)) <$> tzinfoReduceC attr state ∧
    (tzinfoReduceC attr state = tzinfoReducePy attr state → tzinfoReduceClsC ty attr state = tzinfoReduceClsPy ty attr state) ∧
    (∀ r, tzinfoReduceClsC ty attr state = .ok r → r.1 = ty)

theorem tzinfoReduceCls_proven : TzinfoReduceCls := by
  intro α σ ty attr state
  refine ⟨rfl, fun h => by simp only [tzinfoReduceClsC, tzinfoReduceClsPy, h], fun r hr => ?_⟩
  unfold tzinfoReduceClsC at hr
  cases h : tzinfoReduceC attr state with
  | error e => rw [h] at hr; cases hr
  | ok v => rw [h] at hr; cases hr; rfl

end PyLean.Datetime
