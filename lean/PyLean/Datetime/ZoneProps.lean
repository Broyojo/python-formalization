import PyLean.Datetime.ZoneLoadProps
import PyLean.Datetime.ZoneCache

/-!
# Properties of `zoneinfo` lookups, `fromutc`, the TZif reader and the caches (CPython 3.15.2)
-/

namespace PyLean.Datetime.Zone

open PyLean PyLean.Datetime

/-! ### The TZif reader (shared by both twins) -/

/-- `ZoneInfo.from_file` docs: "ValueError is raised if the data read from file_obj is not a
valid TZif file." Every failure of `_common.load_data` is a `ValueError` (or its subclass
`UnicodeDecodeError`). -/
def LoadDataValueError : Prop :=
  ∀ (b : Bytes) (e : PyExc), loadData b = .error e →
    e.className = "ValueError" ∨ e.className = "UnicodeDecodeError"

/-- A header cut after its version byte: `struct.unpack(">6l", ...)` of 23 bytes raises
`struct.error`, which is not a `ValueError`. (A version 2 file without the newline before
its footer raises `AssertionError` the same way.) -/
theorem loadDataValueError_refuted : ¬ LoadDataValueError := by
  intro h
  have := h ([84, 90, 105, 102, 50] ++ List.replicate 38 0)
    (structError "unpack requires a buffer of 24 bytes") (by decide)
  revert this
  decide

/-! ### The footer parsers -/

/-- The Python result of a footer and the C rule describe the same rule. -/
def AfterMatch : After → CRule → Prop
  | .tti t, r => r.stdOnly = true ∧ r.std = t
  | .tzstr z, r => r.stdOnly = false ∧ r.std = z.std ∧ r.dst = z.dst ∧ r.dstDiff = z.dstDiff ∧
      r.start = some z.start ∧ r.end = some z.end

/-- Both parsers accept the same footers with the same rule, and refuse the same ones with a
`ValueError` (Python's `tz_str.decode()` in `_load_file` may raise its subclass
`UnicodeDecodeError`). -/
def TzStrTwinsAgree : Py CRule → Py After → Prop
  | .ok r, .ok a => AfterMatch a r
  | .error _, .error e => e.className = "ValueError" ∨ e.className = "UnicodeDecodeError"
  | _, _ => False

def pyFooter (tz : Bytes) : Py After := if utf8Valid tz then parseTzStrPy tz else .error decodeError

def TzStrTwins : Prop := ∀ tz : Bytes, TzStrTwinsAgree (parseTzStrC tz) (pyFooter tz)

/-- `EST5\0junk`: `PyBytes_AsString` hands C a string that ends at the NUL, so C reads
`EST5`; Python's pattern refuses the whole text. -/
theorem tzStrTwins_refuted : ¬ TzStrTwins := by
  intro h
  have := h [69, 83, 84, 53, 0, 106]
  revert this
  generalize hc : parseTzStrC [69, 83, 84, 53, 0, 106] = pc
  generalize hp : pyFooter [69, 83, 84, 53, 0, 106] = pp
  have h1 : pc.isOk = true := by rw [← hc]; decide
  have h2 : pp.isOk = false := by rw [← hp]; decide
  cases pc <;> cases pp <;> simp_all [Except.isOk, Except.toBool, TzStrTwinsAgree]

/-- Without a NUL byte the parsers agree (open). -/
def TzStrTwinsNoNul : Prop := ∀ tz : Bytes, 0 ∉ tz → TzStrTwinsAgree (parseTzStrC tz) (pyFooter tz)

/-! ### Lookups -/


/-- The fields both twins can hold after the last transition. -/
def AfterCorr (a : After) (r : CRule) : Prop :=
  AfterMatch a r ∧
  match a with
  | .tti _ => True
  | .tzstr z => RuleValid z.start ∧ RuleValid z.end ∧ -2 ^ 40 ≤ z.dstDiff ∧ z.dstDiff ≤ 2 ^ 40 ∧
      -2 ^ 40 ≤ z.std.utcoff ∧ z.std.utcoff ≤ 2 ^ 40 ∧ -2 ^ 40 ≤ z.dst.utcoff ∧ z.dst.utcoff ≤ 2 ^ 40

/-- A Python and a C zone holding the same data: the same transitions in UTC and in local
time, the same `ttinfo` per transition and before the first, the same rule after the last,
and the same fixed-offset flag (which only a `_ttinfo` rule can set). -/
structure Corr (zp : PyZone) (zc : CZone) : Prop where
  trans : zc.transUtc = zp.transUtc
  locals : zc.transLocal = zp.transLocal
  len1 : zp.transLocal.1.length = zp.transUtc.length
  len2 : zp.transLocal.2.length = zp.transUtc.length
  ttinfos : zc.ttinfos = zp.ttinfos
  before : zc.ttiBefore = zp.ttiBefore
  fixed : zc.fixedOffset = zp.fixedOffset
  fixedTti : zp.fixedOffset = true → ∃ t, zp.tzAfter = .tti t
  after : AfterCorr zp.tzAfter zc.rule

/-- A valid `datetime` (`fold` 0 or 1). -/
def ValidDT (y m d h mi s : Int) (fold : Nat) : Prop :=
  1 ≤ y ∧ y ≤ 9999 ∧ 1 ≤ m ∧ m ≤ 12 ∧ 1 ≤ d ∧ d ≤ daysInMonth y m ∧ 0 ≤ h ∧ h < 24 ∧
    0 ≤ mi ∧ mi < 60 ∧ 0 ≤ s ∧ s < 60 ∧ fold ≤ 1

/-- `utcoffset`, `dst` and `tzname` (C `zoneinfo_ZoneInfo_*_impl`, Python `ZoneInfo.*`) read
the same `ttinfo`: for corresponding zones, `None` and every plain `datetime` give the same
lookup. -/
def LookupTwins : Prop :=
  ∀ (zp : PyZone) (zc : CZone), Corr zp zc →
    findTtinfoC zc none = some (findTransPy zp none) ∧
    ∀ (y m d h mi s : Int) (fold : Nat), ValidDT y m d h mi s fold →
      findTtinfoC zc (some (DTObj.ofFields y m d h mi s fold)) =
        some (findTransPy zp (some (DTObj.ofFields y m d h mi s fold)))

theorem bisect_go_eq (a : List Int) (x : Int) :
    ∀ fuel lo hi, lo ≤ hi → bisectC.go x a fuel lo hi = bisectRightPy.go a x fuel lo hi := by
  intro fuel
  induction fuel with
  | zero => intro lo hi _; rfl
  | succ fuel ih =>
    intro lo hi hle
    simp only [bisectC.go, bisectRightPy.go]
    split
    · rename_i hlt
      simp only [gt_iff_lt]
      split
      · exact ih _ _ (by omega)
      · exact ih _ _ (by omega)
    · omega

theorem bisect_eq (a : List Int) (x : Int) : bisectC x a = bisectRightPy a x := by
  unfold bisectC bisectRightPy
  exact bisect_go_eq a x _ _ _ (Nat.zero_le _)

theorem getLast_getD (l : List Int) (h : l ≠ []) : l.getLast?.getD 0 = l.getD (l.length - 1) 0 := by
  rw [List.getLast?_eq_getElem?]
  simp [List.getD_eq_getElem?_getD]

theorem localTs_eq (y m d h mi s : Int) (fold : Nat) (hv : ValidDT y m d h mi s fold) :
    getLocalTsC (DTObj.ofFields y m d h mi s fold) = getLocalTsPy (DTObj.ofFields y m d h mi s fold) := by
  obtain ⟨hy1, hy2, hm1, hm2, hd1, hd2, hh1, hh2, hmi1, hmi2, hs1, hs2, -⟩ := hv
  have ht := month_tables m hm1 hm2
  have hdby := daysBeforeYear_bounds y hy1 hy2
  simp only [getLocalTsC, getLocalTsPy, DTObj.ofFields, ite_true, bind, Except.bind, pure, Except.pure]
  rw [ymdToOrdZ_eq y m d hy1 hy2]
  have hl : 0 ≤ (if m > 2 ∧ isLeap y = true then (1 : Int) else 0) ∧
      (if m > 2 ∧ isLeap y = true then (1 : Int) else 0) ≤ 1 := by constructor <;> split <;> omega
  have hdm : daysInMonth y m ≤ 31 := by unfold daysInMonth; split <;> omega
  rw [wrap64_id, ymd2ord_eq]
  · congr 1
    omega
  · unfold EPOCHORDINAL; omega
  · unfold EPOCHORDINAL; omega

theorem rule_bound (r : TRule) (year : Int) (hv : RuleValid r) (hy : 1 ≤ year) (hy2 : year ≤ 9999) :
    -2 ^ 45 ≤ r.yearToEpochPy year ∧ r.yearToEpochPy year ≤ 2 ^ 45 := by
  have hdby := daysBeforeYear_bounds year hy hy2
  have hl : 0 ≤ (if isLeap year = true then (1 : Int) else 0) := by split <;> omega
  cases r with
  | cal m w d h mi s =>
    obtain ⟨hm1, hm2, hw1, hw2, hd1, hd2, hh1, hh2, hmi1, hmi2, hs1, hs2⟩ := hv
    have ht := month_tables m hm1 hm2
    have hfd : 0 ≤ (ymd2ord year m 1 + 6) % 7 ∧ (ymd2ord year m 1 + 6) % 7 ≤ 6 := by omega
    have hdim : 28 ≤ daysInMonthTable m + (if m = 2 ∧ isLeap year = true then 1 else 0) ∧
        daysInMonthTable m + (if m = 2 ∧ isLeap year = true then 1 else 0) ≤ 31 := by
      constructor <;> split <;> omega
    have hmd := calMonthDayPy_spec _ _ _ _ hfd hdim ⟨hd1, hd2⟩ ⟨hw1, hw2⟩
    simp only at hmd
    simp only [TRule.yearToEpochPy, calYearToEpochPy, monthrange, calWeekday, calYmd2ordPy,
      hy, hy2, and_self, ite_true, postEpoch_eq]
    generalize calMonthDayPy ((ymd2ord year m 1 + 6) % 7)
      (daysInMonthTable m + (if m = 2 ∧ isLeap year = true then 1 else 0)) d w = md at hmd ⊢
    have hl2 : 0 ≤ (if m > 2 ∧ isLeap year = true then (1 : Int) else 0) ∧
        (if m > 2 ∧ isLeap year = true then (1 : Int) else 0) ≤ 1 := by
      constructor <;> split <;> omega
    unfold EPOCHORDINAL
    omega
  | day j d h mi s =>
    obtain ⟨hd1, hd2, hh1, hh2, hmi1, hmi2, hs1, hs2⟩ := hv
    have hj : 0 ≤ d := by split at hd1 <;> omega
    simp only [TRule.yearToEpochPy, dayYearToEpochPy, postEpoch_eq]
    have hb : d ≤ (if j = true ∧ d ≥ 60 ∧ isLeap year = true then d + 1 else d) ∧
        (if j = true ∧ d ≥ 60 ∧ isLeap year = true then d + 1 else d) ≤ d + 1 := by
      constructor <;> split <;> omega
    generalize (if j = true ∧ d ≥ 60 ∧ isLeap year = true then d + 1 else d) = dd at hb ⊢
    unfold EPOCHORDINAL
    omega

theorem isdst_eq (A B ts : Int) :
    (if A < B then decide (ts ≥ A ∧ ts < B) else decide (ts < B ∨ ts ≥ A)) =
      (if A < B then decide (A ≤ ts ∧ ts < B) else !decide (B ≤ ts ∧ ts < A)) := by
  by_cases h : A < B
  · simp only [h, ite_true, ge_iff_le]
  · simp only [h, ite_false]
    by_cases h1 : ts < B <;> by_cases h2 : A ≤ ts <;> simp [h1, h2] <;> omega

theorem rule_find_eq (z : TZStr) (r : CRule) (h : AfterCorr (.tzstr z) r) (ts year : Int)
    (fold : Nat) (hy : 1 ≤ year) (hy2 : year ≤ 9999) (hts : -2 ^ 50 ≤ ts ∧ ts ≤ 2 ^ 50)
    (hf : fold ≤ 1) : r.find ts fold year = z.getTransInfo ts year fold := by
  obtain ⟨⟨hso, hstd, hdst, hdd, hs, he⟩, hv1, hv2, hb1, hb2, -⟩ := h
  have t1 := ruleDateTwins_proven z.start year hv1 hy hy2
  have t2 := ruleDateTwins_proven z.end year hv2 hy hy2
  have b1 := rule_bound z.start year hv1 hy hy2
  have b2 := rule_bound z.end year hv2 hy hy2
  unfold CRule.find TZStr.getTransInfo CRule.transitions TZStr.transitions
  simp only [hso, hs, he, Option.getD_some, t1, t2, hdd, hstd, hdst, Bool.false_eq_true, ite_false]
  generalize z.start.yearToEpochPy year = A at b1 ⊢
  generalize z.end.yearToEpochPy year = B at b2 ⊢
  rcases (by omega : fold = 0 ∨ fold = 1) with rfl | rfl <;> by_cases hd : z.dstDiff ≥ 0 <;>
    simp (config := { decide := true }) only [hd, ite_true, ite_false] <;>
    first
    | rw [wrap64_id (B - z.dstDiff) (by omega) (by omega), isdst_eq]
    | rw [wrap64_id (A + z.dstDiff) (by omega) (by omega), isdst_eq]

theorem lookupTwins_proven : LookupTwins := by
  intro zp zc hc
  refine ⟨?_, ?_⟩
  · simp only [findTtinfoC, findTransPy, hc.fixed]
    cases hf : zp.fixedOffset
    · rfl
    · obtain ⟨t, ht⟩ := hc.fixedTti hf
      have ha := hc.after
      rw [ht] at ha
      obtain ⟨⟨-, hstd⟩, -⟩ := ha
      simp [ht, hstd]
  · intro y m d h mi s fold hv
    have hts := localTs_eq y m d h mi s fold hv
    obtain ⟨hy1, hy2, hm1, hm2, hd1, hd2, hh1, hh2, hmi1, hmi2, hs1, hs2, hf⟩ := hv
    have ht := month_tables m hm1 hm2
    have hdby := daysBeforeYear_bounds y hy1 hy2
    have hdm : daysInMonth y m ≤ 31 := by unfold daysInMonth; split <;> omega
    have hl : 0 ≤ (if m > 2 ∧ isLeap y = true then (1 : Int) else 0) ∧
        (if m > 2 ∧ isLeap y = true then (1 : Int) else 0) ≤ 1 := by constructor <;> split <;> omega
    simp only [findTtinfoC, findTransPy]
    rw [hts]
    simp only [getLocalTsPy, DTObj.ofFields, bind, Except.bind, pure, Except.pure]
    generalize hT : (ymd2ord y m d - EPOCHORDINAL) * 86400 + h * 3600 + mi * 60 + s = ts
    have htsb : -2 ^ 50 ≤ ts ∧ ts ≤ 2 ^ 50 := by
      rw [← hT, ymd2ord_eq]; unfold EPOCHORDINAL; omega
    rw [hc.trans, hc.locals, hc.ttinfos, hc.before]
    rcases (by omega : fold = 0 ∨ fold = 1) with rfl | rfl
    all_goals
      simp (config := { decide := true }) only [Bool.not_true, Bool.false_eq_true, ite_false,
        ite_true, true_or, or_true, hc.len1, hc.len2]
      by_cases hn : zp.transUtc.length = 0
      · simp only [hn, ne_eq, not_true_eq_false, false_and, ite_false, true_or, ite_true]
        have ha := hc.after
        cases hta : zp.tzAfter with
        | tti t =>
          rw [hta] at ha
          obtain ⟨⟨hso, hstd⟩, -⟩ := ha
          simp [CRule.find, hso, hstd]
        | tzstr z =>
          rw [hta] at ha
          simp only [Except.ok.injEq, Option.some.injEq]
          exact rule_find_eq z zc.rule ha ts y _ hy1 hy2 htsb (by omega)
      · have hne1 : zp.transLocal.1 ≠ [] := by
          intro e; have := hc.len1; rw [e] at this; simp at this; omega
        have hne2 : zp.transLocal.2 ≠ [] := by
          intro e; have := hc.len2; rw [e] at this; simp at this; omega
        simp only [hn, ne_eq, not_false_eq_true, true_and, false_or, getLast_getD _ hne1,
          getLast_getD _ hne2, hc.len1, hc.len2, bisect_eq]
        split
        · rfl
        · split
          · have ha := hc.after
            cases hta : zp.tzAfter with
            | tti t =>
              rw [hta] at ha
              obtain ⟨⟨hso, hstd⟩, -⟩ := ha
              simp [CRule.find, hso, hstd]
            | tzstr z =>
              rw [hta] at ha
              simp only [Except.ok.injEq, Option.some.injEq]
              exact rule_find_eq z zc.rule ha ts y _ hy1 hy2 htsb (by omega)
          · rfl

/-- `ZoneInfo.utcoffset`/`dst`/`tzname` (_zoneinfo.py:109-116): `self._find_trans(dt)` and
one field. -/
def utcoffsetPy (z : PyZone) (dt : Option DTObj) : Py (Option Int) := (findTransPy z dt).map (·.map TTI.utcoff)
def dstPy (z : PyZone) (dt : Option DTObj) : Py (Option Int) := (findTransPy z dt).map (·.map TTI.dstoff)
def tznamePy (z : PyZone) (dt : Option DTObj) : Py (Option Bytes) := (findTransPy z dt).map (·.map TTI.tzname)

/-- C `zoneinfo_ZoneInfo_utcoffset_impl`/`_dst_impl`/`_tzname_impl` (Modules/_zoneinfo.c:580-638):
`find_ttinfo`, `NULL` on error, else a new reference to one field. -/
def utcoffsetC (z : CZone) (dt : Option DTObj) : Option (Py (Option Int)) :=
  (findTtinfoC z dt).map (·.map (·.map TTI.utcoff))
def dstC (z : CZone) (dt : Option DTObj) : Option (Py (Option Int)) :=
  (findTtinfoC z dt).map (·.map (·.map TTI.dstoff))
def tznameC (z : CZone) (dt : Option DTObj) : Option (Py (Option Bytes)) :=
  (findTtinfoC z dt).map (·.map (·.map TTI.tzname))

/-- The three methods agree between the twins on corresponding zones, for `None` and every
plain `datetime`. -/
def LookupMethodsTwins : Prop :=
  ∀ (zp : PyZone) (zc : CZone), Corr zp zc → ∀ dt : Option DTObj,
    (dt = none ∨ ∃ y m d h mi s fold, ValidDT y m d h mi s fold ∧ dt = some (DTObj.ofFields y m d h mi s fold)) →
    utcoffsetC zc dt = some (utcoffsetPy zp dt) ∧ dstC zc dt = some (dstPy zp dt) ∧
      tznameC zc dt = some (tznamePy zp dt)

theorem lookupMethodsTwins_proven : LookupMethodsTwins := by
  intro zp zc hc dt hdt
  have hf : findTtinfoC zc dt = some (findTransPy zp dt) := by
    rcases hdt with rfl | ⟨y, m, d, h, mi, s, fold, hv, rfl⟩
    · exact (lookupTwins_proven zp zc hc).1
    · exact (lookupTwins_proven zp zc hc).2 y m d h mi s fold hv
  simp only [utcoffsetC, dstC, tznameC, utcoffsetPy, dstPy, tznamePy, hf, Option.map_some,
    and_self]

/-- No argument makes C `find_ttinfo` read memory it does not own: every object whose
`toordinal()`, `hour`, `minute` and `second` C can read gets a defined result. -/
def FindTtinfoDefined : Prop :=
  ∀ (zc : CZone) (dt : DTObj), (getLocalTsC dt).isOk = true → (findTtinfoC zc (some dt)).isSome = true

/-- An object with `toordinal()`, `hour`, `minute` and `second` that is not a `datetime`:
`get_local_timestamp` succeeds through the attributes, then `find_ttinfo` reads the fold byte
of a `datetime` struct the object does not have (gh-125318; the Python twin raises
`AttributeError` on `dt.fold`). -/
theorem findTtinfoDefined_refuted : ¬ FindTtinfoDefined := by
  intro h
  have := h ⟨[], ([], []), [], none, default, false⟩
    ⟨false, false, 0, 0, 0, 0, 0, 0, 0, .ok 738000, .ok 0, .ok 0, .ok 0,
      .error (.named "AttributeError" "~"), .error (.named "AttributeError" "~")⟩ (by decide)
  revert this
  decide

/-! ### `fromutc` -/

/-- `fromutc` adds the same offset and sets the same fold in both twins, for corresponding
zones and every plain `datetime` whose `tzinfo` is the zone. -/
def FromutcTwins : Prop :=
  ∀ (zp : PyZone) (zc : CZone), Corr zp zc → ∀ (y m d h mi s : Int), ValidDT y m d h mi s 0 →
    fromutcC zc (DTObj.ofFields y m d h mi s 0) true = fromutcPy zp (DTObj.ofFields y m d h mi s 0) true

def ttiA : TTI := ⟨10800, 0, [65, 65, 65]⟩
def ttiB : TTI := ⟨7200, 0, [66, 66, 66]⟩
def ttiC : TTI := ⟨10800, 3600, [67, 67, 67]⟩
def ruleBC : TZStr := ⟨ttiB, ttiC, 3600, .cal 3 5 0 2 0 0, .cal 10 5 0 3 0 0⟩
/-- 2001-11-15 00:00 UTC: the standard offset drops from +3 to +2 (`BBB-2CCC-3,M3.5.0,M10.5.0/3`
after it). -/
def foldZoneT : Int := 1005782400
def foldZonePy : PyZone :=
  ⟨[foldZoneT], ([foldZoneT + 10800], [foldZoneT + 7200]), [ttiB], some ttiA, .tzstr ruleBC, false⟩
def foldZoneC : CZone :=
  ⟨[foldZoneT], ([foldZoneT + 10800], [foldZoneT + 7200]), [ttiB], some ttiA,
    ⟨ttiB, ttiC, 3600, some ruleBC.start, some ruleBC.end, false⟩, false⟩

theorem foldZone_corr : Corr foldZonePy foldZoneC :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun h => absurd h (by decide),
    ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, by simp only [foldZonePy, ruleBC, RuleValid, ttiB, ttiC]; decide⟩⟩

/-- 00:30 UTC, half an hour after that transition: 02:30 local time happened before at +3,
so C sets `fold=1`; Python asks only the footer rule and leaves `fold=0` (gh-159707). -/
theorem fromutcTwins_refuted : ¬ FromutcTwins := by
  intro h
  have := h foldZonePy foldZoneC foldZone_corr 2001 11 15 0 30 0 (by unfold ValidDT; decide)
  revert this
  decide

theorem rule_fromutc_eq (z : TZStr) (r : CRule) (h : AfterCorr (.tzstr z) r) (ts year : Int)
    (hy : 1 ≤ year) (hy2 : year ≤ 9999) (hts : -2 ^ 50 ≤ ts ∧ ts ≤ 2 ^ 50) :
    r.findFromutc ts year = z.getTransInfoFromutc ts year := by
  obtain ⟨⟨hso, hstd, hdst, hdd, hs, he⟩, hv1, hv2, hb1, hb2, hu1, hu2, hu3, hu4⟩ := h
  have t1 := ruleDateTwins_proven z.start year hv1 hy hy2
  have t2 := ruleDateTwins_proven z.end year hv2 hy hy2
  have b1 := rule_bound z.start year hv1 hy hy2
  have b2 := rule_bound z.end year hv2 hy hy2
  unfold CRule.findFromutc TZStr.getTransInfoFromutc CRule.transitions TZStr.transitions
  simp only [hso, hs, he, Option.getD_some, t1, t2, hdd, hstd, hdst, Bool.false_eq_true, ite_false]
  generalize z.start.yearToEpochPy year = A at b1 ⊢
  generalize z.end.yearToEpochPy year = B at b2 ⊢
  rw [wrap64_id (A - z.std.utcoff) (by omega) (by omega),
    wrap64_id (B - z.dst.utcoff) (by omega) (by omega), isdst_eq]
  by_cases hd : z.dstDiff > 0
  · simp only [hd, ite_true, ge_iff_le]
    rw [wrap64_id (B - z.dst.utcoff + z.dstDiff) (by omega) (by omega)]
  · simp only [hd, ite_false, ge_iff_le]
    rw [wrap64_id (A - z.std.utcoff - z.dstDiff) (by omega) (by omega)]

/-- With no explicit transitions (a zone given by its footer alone) the twins agree. -/
def FromutcTwinsNoTrans : Prop :=
  ∀ (zp : PyZone) (zc : CZone), Corr zp zc → zp.transUtc = [] →
    ∀ (y m d h mi s : Int), ValidDT y m d h mi s 0 →
      fromutcC zc (DTObj.ofFields y m d h mi s 0) true = fromutcPy zp (DTObj.ofFields y m d h mi s 0) true

theorem fromutcTwinsNoTrans_proven : FromutcTwinsNoTrans := by
  intro zp zc hc hnil y m d h mi s hv
  have hts := localTs_eq y m d h mi s 0 hv
  obtain ⟨hy1, hy2, hm1, hm2, hd1, hd2, hh1, hh2, hmi1, hmi2, hs1, hs2, -⟩ := hv
  have ht := month_tables m hm1 hm2
  have hdby := daysBeforeYear_bounds y hy1 hy2
  have hdm : daysInMonth y m ≤ 31 := by unfold daysInMonth; split <;> omega
  have hl : 0 ≤ (if m > 2 ∧ isLeap y = true then (1 : Int) else 0) ∧
      (if m > 2 ∧ isLeap y = true then (1 : Int) else 0) ≤ 1 := by constructor <;> split <;> omega
  unfold fromutcC fromutcPy fromutcCoreC fromutcCorePy
  rw [hts]
  simp only [getLocalTsPy, DTObj.ofFields, bind, Except.bind, pure, Except.pure, Bool.not_true,
    Bool.false_eq_true, ite_false, hc.trans, hnil, List.length_nil]
  generalize hT : (ymd2ord y m d - EPOCHORDINAL) * 86400 + h * 3600 + mi * 60 + s = ts
  have htsb : -2 ^ 50 ≤ ts ∧ ts ≤ 2 ^ 50 := by
    rw [← hT, ymd2ord_eq]; unfold EPOCHORDINAL; omega
  have ha := hc.after
  cases hta : zp.tzAfter with
  | tti t =>
    rw [hta] at ha
    obtain ⟨⟨hso, hstd⟩, -⟩ := ha
    simp (config := { decide := true }) [CRule.findFromutc, hso, hstd]
  | tzstr z =>
    rw [hta] at ha
    dsimp only
    simp only [show ¬ ((0 : Nat) ≥ 1) by decide, false_and, ite_false, true_or, true_and,
      Option.isSome_some, ite_true, ne_eq, not_true_eq_false]
    rw [rule_fromutc_eq z zc.rule ha ts y hy1 hy2 htsb]
    rfl

/-! ### The strong cache -/

section cache

variable {K : Type} [DecidableEq K]

/-- The twins' states correspond: C's list is Python's order reversed, the weak caches are
equal, and the strong cache holds distinct keys, at most 8, all alive in the weak cache. -/
structure CInv (sp sc : CacheSt K) : Prop where
  strong : sc.strong = sp.strong.reverse
  weak : sc.weak = sp.weak
  nodup : sp.strong.Nodup
  sub : ∀ k ∈ sp.strong, k ∈ sp.weak
  len : sp.strong.length ≤ 8

theorem nodup_rev (l : List K) (h : l.Nodup) : l.reverse.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a l ih =>
    rw [List.nodup_cons] at h
    rw [List.reverse_cons, List.nodup_append]
    refine ⟨ih h.2, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩
    intro x hx b hb
    simp at hb hx
    subst hb
    intro e; subst e; exact h.1 hx

theorem erase_reverse (l : List K) (k : K) (h : l.Nodup) :
    (l.erase k).reverse = l.reverse.erase k := by
  rw [h.erase_eq_filter k, (nodup_rev l h).erase_eq_filter k, List.filter_reverse]

theorem insert_rev (s : List K) (k : K) (hk : k ∉ s) (hnd : s.Nodup) (hl : s.length ≤ 8) :
    (k :: s.reverse).take 8 = (if (s ++ [k]).length > 8 then (s ++ [k]).tail else s ++ [k]).reverse ∧
    (if (s ++ [k]).length > 8 then (s ++ [k]).tail else s ++ [k]).Nodup ∧
    (∀ x ∈ (if (s ++ [k]).length > 8 then (s ++ [k]).tail else s ++ [k]), x ∈ s ∨ x = k) ∧
    (if (s ++ [k]).length > 8 then (s ++ [k]).tail else s ++ [k]).length ≤ 8 := by
  have hnd2 : (s ++ [k]).Nodup := by
    rw [List.nodup_append]
    refine ⟨hnd, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩
    intro a ha b hb
    simp at hb; subst hb
    intro e; subst e; exact hk ha
  by_cases hlt : s.length < 8
  · have : ¬ ((s ++ [k]).length > 8) := by simp; omega
    simp only [this, ite_false]
    refine ⟨?_, hnd2, fun x hx => by simpa using hx, by simp; omega⟩
    rw [List.take_of_length_le (by simp; omega)]
    simp
  · have hl8 : s.length = 8 := by omega
    have : (s ++ [k]).length > 8 := by simp; omega
    simp only [this, ite_true]
    cases s with
    | nil => simp at hl8
    | cons a s' =>
      simp only [List.cons_append, List.tail_cons]
      simp only [List.length_cons] at hl8
      refine ⟨?_, ?_, ?_, by simp; omega⟩
      · rw [List.reverse_cons, List.take_succ_cons, List.take_append_of_le_length (by simp; omega),
          List.reverse_append]
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
          List.cons.injEq, true_and]
        exact List.take_of_length_le (by simp only [List.length_reverse]; omega)
      · rw [List.cons_append, List.nodup_cons] at hnd2
        exact hnd2.2
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | hx
        · exact .inl (List.mem_cons_of_mem _ hx)
        · exact .inr hx

theorem clearKeys_inv (ks : List K) : ∀ (sp sc : CacheSt K), CInv sp sc →
    CInv (ks.foldl (fun st k => ⟨st.strong.erase k, st.weak.erase k⟩) sp)
      (ks.foldl (fun st k => ⟨st.strong.erase k, st.weak.erase k⟩) sc) := by
  induction ks with
  | nil => intro sp sc h; exact h
  | cons k ks ih =>
    intro sp sc h
    apply ih
    refine ⟨?_, ?_, h.nodup.erase k, ?_, ?_⟩
    · simp only [h.strong, erase_reverse _ _ h.nodup]
    · simp only [h.weak]
    · intro x hx
      rw [h.nodup.mem_erase_iff] at hx
      exact List.mem_erase_of_ne hx.1 |>.mpr (h.sub x hx.2)
    · have := List.length_erase_le (l := sp.strong) (a := k); simp only; have := h.len; omega

theorem step_inv (loads : K → Bool) (sp sc : CacheSt K) (h : CInv sp sc) (op : CacheOp K) :
    match stepPy loads sp op, stepC loads sc op with
    | some sp', some sc' => CInv sp' sc'
    | none, none => True
    | _, _ => False := by
  have hmem : ∀ k, k ∈ sc.strong ↔ k ∈ sp.strong := fun k => by rw [h.strong, List.mem_reverse]
  cases op with
  | get k =>
    simp only [stepPy, stepC, newPy, newC]
    by_cases hk : k ∈ sp.strong
    · have hw : k ∈ sp.weak := h.sub k hk
      simp only [(hmem k).mpr hk, hw, ite_true, Option.map_some]
      have hlen : (sp.strong.erase k ++ [k]).length = sp.strong.length := by
        simp [List.length_erase_of_mem hk]; have := List.length_pos_of_mem hk; omega
      have : ¬ ((sp.strong.erase k ++ [k]).length > 8) := by rw [hlen]; have := h.len; omega
      simp only [this, ite_false]
      refine ⟨?_, h.weak, ?_, ?_, by rw [hlen]; exact h.len⟩
      · simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.cons_append, h.strong, erase_reverse _ _ h.nodup]
      · rw [List.nodup_append]
        refine ⟨h.nodup.erase k, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩
        intro a ha b hb
        simp at hb; subst hb
        intro e; subst e
        exact h.nodup.not_mem_erase ha
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact h.sub x (List.mem_of_mem_erase hx)
        · exact hw
    · have hk' : k ∉ sc.strong := fun e => hk ((hmem k).mp e)
      simp only [hk', ite_false, h.weak, List.erase_of_not_mem hk]
      by_cases hw : k ∈ sp.weak
      · simp only [hw, ite_true, Option.map_some]
        obtain ⟨e1, e2, e3, e4⟩ := insert_rev sp.strong k hk h.nodup h.len
        refine ⟨by rw [h.strong]; exact e1, rfl, e2, fun x hx => ?_, e4⟩
        rcases e3 x hx with hx | hx
        · exact h.sub x hx
        · rw [hx]; exact hw
      · by_cases hl : loads k = true
        · simp only [hw, hl, ite_false, ite_true, Option.map_some]
          obtain ⟨e1, e2, e3, e4⟩ := insert_rev sp.strong k hk h.nodup h.len
          refine ⟨by rw [h.strong]; exact e1, rfl, e2, fun x hx => ?_, e4⟩
          rcases e3 x hx with hx | hx
          · exact List.mem_cons_of_mem _ (h.sub x hx)
          · rw [hx]; exact List.mem_cons_self
        · simp only [hw, hl, ite_false, Bool.false_eq_true, Option.map_none]
  | clear =>
    simp only [stepPy, stepC, clearPy, clearC]
    exact ⟨rfl, rfl, List.nodup_nil, by simp, by simp⟩
  | clearKeys ks =>
    simp only [stepPy, stepC, clearPy, clearC]
    exact clearKeys_inv ks sp sc h
  | drop k =>
    simp only [stepPy, stepC]
    refine ⟨h.strong, ?_, h.nodup, ?_, h.len⟩
    · simp only [hmem k, h.weak]
    · intro x hx
      simp only
      split
      · exact h.sub x hx
      · rename_i hk
        exact (List.mem_erase_of_ne (fun e => hk (by rw [← e]; exact hx))).mpr (h.sub x hx)

theorem run_inv (loads : K → Bool) : ∀ (ops : List (CacheOp K)) (sp sc : CacheSt K), CInv sp sc →
    CInv (runPy loads sp ops).1 (runC loads sc ops).1 ∧ (runC loads sc ops).2 = (runPy loads sp ops).2 := by
  intro ops
  induction ops with
  | nil => intro sp sc h; exact ⟨h, rfl⟩
  | cons op ops ih =>
    intro sp sc h
    have hs := step_inv loads sp sc h op
    simp only [runPy, runC]
    cases hp : stepPy loads sp op <;> cases hc : stepC loads sc op <;> rw [hp, hc] at hs
    · have := ih sp sc h
      exact ⟨this.1, by simp [this.2]⟩
    · exact hs.elim
    · exact hs.elim
    · have := ih _ _ hs
      exact ⟨this.1, by simp [this.2]⟩

end cache

/-- The primary constructor's strong cache: for every run of `ZoneInfo(key)` and
`clear_cache` calls on the base class, both twins raise for the same calls and hold the same
keys in the same recency order (C newest first, Python oldest first), never more than
`_strong_cache_size = 8`. -/
def CacheTwins : Prop :=
  ∀ (K : Type) [DecidableEq K] (loads : K → Bool) (ops : List (CacheOp K)),
    (runC loads ⟨[], []⟩ ops).1.strong = (runPy loads ⟨[], []⟩ ops).1.strong.reverse ∧
    (runC loads ⟨[], []⟩ ops).2 = (runPy loads ⟨[], []⟩ ops).2 ∧
    (runPy loads ⟨[], []⟩ ops).1.strong.length ≤ 8

theorem cacheTwins_proven : CacheTwins := by
  intro K _ loads ops
  have := run_inv loads ops ⟨[], []⟩ ⟨[], []⟩ ⟨rfl, rfl, List.nodup_nil, by simp, by simp⟩
  exact ⟨this.1.strong, this.2, this.1.len⟩

end PyLean.Datetime.Zone

namespace PyLean.Datetime.Zone

/-- `_common.load_data` returns well-formed data: list lengths match, indices name types, and
the values fit their `struct` formats (open). -/
def LoadDataShape : Prop := ∀ (b : Bytes) (d : TzifData), loadData b = .ok d → TzifShape d

/-- From the same well-formed tuple, with 0/1 flags, offsets below `2**30`, no `int64_t`
overflow and a footer without NUL (the cases refuted above), `_load_file` and C `load_data`
build corresponding zones or both raise (open). -/
def LoadTwins : Prop :=
  ∀ d : TzifData, TzifShape d → (∀ x ∈ d.isdst, x = 0 ∨ x = 1) →
    (∀ u ∈ d.utcoff, -2 ^ 30 ≤ u ∧ u < 2 ^ 30) →
    (∀ t ∈ d.transUtc, ∀ u ∈ d.utcoff, -2 ^ 63 ≤ t + u ∧ t + u < 2 ^ 63) →
    (∀ s, d.tzStr = some s → 0 ∉ s) →
    match loadFilePy d, loadDataC d with
    | .ok zp, .ok zc => Corr zp zc
    | .error _, .error _ => True
    | _, _ => False

end PyLean.Datetime.Zone

namespace PyLean.Datetime.Zone

/-- `_common.load_data` reports a malformed file with an exception, never with a failed
`assert` (an internal check that `python -O` removes). -/
def LoadDataNoAssertion : Prop :=
  ∀ (b : Bytes) (e : PyExc), loadData b = .error e → e.className ≠ "AssertionError"

/-- A complete version 2 file whose footer lacks its leading newline: the two headers, the
type record and the designation read fine, then `assert c == b"\n", c` (_common.py:123)
fails on `b'U'`. -/
def noNewlineFile : Bytes :=
  [84, 90, 105, 102, 50] ++ List.replicate 39 0 ++
  [84, 90, 105, 102, 50] ++ List.replicate 15 0 ++
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4] ++
  [0, 0, 0, 0, 0, 0] ++ [85, 84, 67, 0] ++ [85, 84, 67, 48, 10]

theorem loadDataNoAssertion_refuted : ¬ LoadDataNoAssertion := by
  intro h
  have := h noNewlineFile (.assertionError "b'U'") (by decide)
  revert this
  decide

/-- The lookups agree for every `datetime` instance, subclasses included: an instance of a
subclass has valid struct fields, and its attributes are whatever the subclass returns. -/
def LookupTwinsInstances : Prop :=
  ∀ (zp : PyZone) (zc : CZone), Corr zp zc → ∀ dt : DTObj, dt.isDatetime = true →
    ValidDT dt.y dt.m dt.d dt.h dt.mi dt.s dt.fold →
    findTtinfoC zc (some dt) = some (findTransPy zp (some dt))

def subZonePy : PyZone :=
  ⟨[2 ^ 40], ([2 ^ 40], [2 ^ 40]), [⟨25200, 0, [66]⟩], some ⟨0, 0, [65]⟩, .tti ⟨25200, 0, [66]⟩, false⟩
def subZoneC : CZone :=
  ⟨[2 ^ 40], ([2 ^ 40], [2 ^ 40]), [⟨25200, 0, [66]⟩], some ⟨0, 0, [65]⟩,
    ⟨⟨25200, 0, [66]⟩, default, 0, none, none, true⟩, false⟩

/-- A subclass instance for 2021-01-01 whose `toordinal()` returns its ordinal plus `2**32`:
C narrows it to `int` (`PyLong_AsLong` into `int ord`, Modules/_zoneinfo.c:2307) and lands
before the transition at `2**40` (+00:00), Python keeps the int and lands after it (+07:00). -/
theorem lookupTwinsInstances_refuted : ¬ LookupTwinsInstances := by
  intro h
  have := h subZonePy subZoneC
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun h => absurd h (by decide), ⟨⟨rfl, rfl⟩, trivial⟩⟩
    ⟨true, false, 2021, 1, 1, 0, 0, 0, 0, .ok (ymd2ord 2021 1 1 + 2 ^ 32), .ok 0, .ok 0, .ok 0,
      .ok 0, .ok 2021⟩ rfl (by unfold ValidDT; decide)
  revert this
  decide

end PyLean.Datetime.Zone

namespace PyLean.Datetime.Zone

/-- The twins keep the same zones alive through a subclass's strong cache: after the class
statement runs `__init_subclass__`, every run of `Sub(key)` calls leaves the same keys there. -/
def CacheTwinsSubclass : Prop :=
  ∀ (K : Type) [DecidableEq K] (loads : K → Bool) (wvd : Py Unit) (ks : List K) (sp sc : CacheSt K),
    initSubclassPy wvd = .ok sp → initSubclassC wvd = .ok sc →
    (runSubC loads sc ks).strong = (runSubPy loads sp ks).strong.reverse

/-- One `Sub(key)`: Python's subclass keeps the zone in its own strong cache, C keeps none, so
the zone dies with its last outside reference in C only. -/
theorem cacheTwinsSubclass_refuted : ¬ CacheTwinsSubclass := by
  intro h
  have := h Nat (fun _ => true) (.ok ()) [0] ⟨[], []⟩ ⟨[], []⟩ rfl rfl
  revert this
  decide

/-- `ZoneInfo.clear_cache()` never makes C read or free memory twice, whatever the keys'
finalizers do. -/
def ClearCacheDefined : Prop :=
  ∀ (K : Type) [DecidableEq K] (loads : K → Bool) (dels : K → List K) (st : CacheSt K),
    st.strong.Nodup → st.strong.length ≤ 8 → (clearStrongC loads dels st).isSome = true

/-- Three cached keys whose finalizers each call `ZoneInfo(...)` with a new key: the finalizer
of the second node runs after the first node was freed, while the cache head still points at it
(the recorded segfault). -/
theorem clearCacheDefined_refuted : ¬ ClearCacheDefined := by
  intro h
  have := h Nat (fun _ => true) (fun k => [k + 3]) ⟨[0, 1, 2], [0, 1, 2]⟩ (by decide) (by decide)
  revert this
  decide

/-- Looking a key up in the C strong cache never reads freed memory, whatever the keys'
`__eq__` does. -/
def StrongLookupDefined : Prop :=
  ∀ (K : Type) (eq clears : K → K → Bool) (key : K) (strong : List K),
    (findInStrongC eq clears key strong).isSome = true

/-- A key whose `__eq__` calls `ZoneInfo.clear_cache()` (gh-142782): the walk continues to
`node->next` of a freed node. -/
theorem strongLookupDefined_refuted : ¬ StrongLookupDefined := by
  intro h
  have := h Nat (fun _ _ => false) (fun _ _ => true) 5 [0, 1]
  revert this
  decide

end PyLean.Datetime.Zone

namespace PyLean.Datetime.Zone

/-! ### `fromutc` with explicit transitions -/

/-- For zones whose rule after the last transition is a fixed `_ttinfo` (the footer has no
DST), the twins add the same offset and set the same fold. -/
def FromutcTwinsStatic : Prop :=
  ∀ (zp : PyZone) (zc : CZone), Corr zp zc → (∃ t, zp.tzAfter = .tti t) →
    ∀ (y m d h mi s : Int), ValidDT y m d h mi s 0 →
      fromutcC zc (DTObj.ofFields y m d h mi s 0) true = fromutcPy zp (DTObj.ofFields y m d h mi s 0) true

def ttX : TTI := ⟨0, 0, [88]⟩
def staticPy : PyZone :=
  ⟨[0, 1000], ([3600, 8200], [3600, 4600]), [⟨3600, 0, [66]⟩, ⟨7200, 0, [67]⟩], some ⟨0, 0, [65]⟩,
    .tti ttX, false⟩
def staticC : CZone :=
  ⟨[0, 1000], ([3600, 8200], [3600, 4600]), [⟨3600, 0, [66]⟩, ⟨7200, 0, [67]⟩], some ⟨0, 0, [65]⟩,
    ⟨ttX, default, 0, none, none, true⟩, false⟩

/-- Two transitions (to +1h, then +2h) and the footer `XXX0`: after the last transition C adds
the footer's +00:00, Python the last transition's +02:00 (`self._ttinfos[idx - 2 : idx]`,
_zoneinfo.py:144-145), although Python's own `utcoffset` of the result is +00:00. -/
theorem fromutcTwinsStatic_refuted : ¬ FromutcTwinsStatic := by
  intro h
  have := h staticPy staticC
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun h => absurd h (by decide), ⟨⟨rfl, rfl⟩, trivial⟩⟩
    ⟨_, rfl⟩ 2000 1 1 0 0 0 (by unfold ValidDT; decide)
  revert this
  decide

/-- Transition times in ascending order, as RFC 9636 §3.2 requires. -/
def SortedL (a : List Int) : Prop := ∀ i j, i < j → j < a.length → a.getD i 0 ≤ a.getD j 0

theorem bisect_spec (a : List Int) (x : Int) (hs : SortedL a) :
    ∀ fuel lo hi, lo ≤ hi → hi ≤ a.length → hi - lo < fuel →
      (∀ j, j < lo → a.getD j 0 ≤ x) → (∀ j, hi ≤ j → j < a.length → x < a.getD j 0) →
      bisectRightPy.go a x fuel lo hi ≤ a.length ∧
      (∀ j, j < bisectRightPy.go a x fuel lo hi → a.getD j 0 ≤ x) ∧
      (∀ j, bisectRightPy.go a x fuel lo hi ≤ j → j < a.length → x < a.getD j 0) := by
  intro fuel
  induction fuel with
  | zero => intro lo hi _ _ h; omega
  | succ fuel ih =>
    intro lo hi hle hhi hf hlo hhi'
    simp only [bisectRightPy.go]
    split
    · rename_i hlt
      have hm1 : lo ≤ (lo + hi) / 2 := by omega
      have hm2 : (lo + hi) / 2 < hi := by omega
      split
      · rename_i hx
        apply ih lo ((lo + hi) / 2) hm1 (by omega) (by omega) hlo
        intro j hj hjl
        rcases Nat.lt_or_ge ((lo + hi) / 2) j with e | e
        · exact Int.lt_of_lt_of_le hx (hs _ _ e hjl)
        · have : j = (lo + hi) / 2 := by omega
          rw [this]; exact hx
      · rename_i hx
        apply ih ((lo + hi) / 2 + 1) hi (by omega) hhi (by omega) _ hhi'
        intro j hj
        rcases Nat.lt_or_ge j lo with e | e
        · exact hlo j e
        · rcases Nat.lt_or_ge j ((lo + hi) / 2) with e2 | e2
          · exact Int.le_trans (hs _ _ e2 (by omega)) (by omega)
          · have : j = (lo + hi) / 2 := by omega
            rw [this]; omega
    · have : lo = hi := by omega
      subst this
      exact ⟨hhi, hlo, hhi'⟩

theorem slice_two (l : List TTI) (k : Nat) (h : k + 2 ≤ l.length) :
    (l.drop k).take 2 = [l.getD k default, l.getD (k + 1) default] := by
  induction l generalizing k with
  | nil => simp at h
  | cons x xs ih =>
    cases k with
    | zero =>
      cases xs with
      | nil => simp at h
      | cons y ys => simp
    | succ k =>
      simp only [List.drop_succ_cons, List.getD_cons_succ]
      exact ih k (by simp at h; omega)

theorem pySlice_two (l : List TTI) (i : Nat) (h1 : 2 ≤ i) (h2 : i ≤ l.length) :
    pySlice l ((i : Int) - 2) i = [l.getD (i - 2) default, l.getD (i - 1) default] := by
  unfold pySlice sliceIdx
  have e1 : ¬ ((i : Int) - 2 < 0) := by omega
  have e2 : ¬ ((i : Int) < 0) := by omega
  simp only [e1, e2, ite_false]
  have : min ((i : Int) - 2).toNat l.length = i - 2 := by omega
  have h3 : min (i : Int).toNat l.length = i := by omega
  rw [this, h3, show i - (i - 2) = 2 by omega, slice_two l (i - 2) (by omega),
    show i - 2 + 1 = i - 1 by omega]

theorem tti_bound (l : List TTI) (hb : ∀ t ∈ l, -2 ^ 40 ≤ t.utcoff ∧ t.utcoff ≤ 2 ^ 40) (k : Nat) :
    -2 ^ 40 ≤ (l.getD k default).utcoff ∧ (l.getD k default).utcoff ≤ 2 ^ 40 := by
  induction l generalizing k with
  | nil => simp; decide
  | cons x xs ih =>
    cases k with
    | zero => simpa using hb x (by simp)
    | succ k =>
      simp only [List.getD_cons_succ]
      exact ih (fun t ht => hb t (by simp [ht])) k

theorem int_bound (l : List Int) (hb : ∀ t ∈ l, -2 ^ 62 ≤ t ∧ t ≤ 2 ^ 62) (k : Nat) :
    -2 ^ 62 ≤ l.getD k 0 ∧ l.getD k 0 ≤ 2 ^ 62 :=
  getD_prop l _ hb (by decide) k

end PyLean.Datetime.Zone

namespace PyLean.Datetime.Zone

theorem getLast_getD_tti (l : List TTI) (h : l ≠ []) :
    l.getLast?.getD default = l.getD (l.length - 1) default := by
  rw [List.getLast?_eq_getElem?]
  simp [List.getD_eq_getElem?_getD]

theorem pyGet_pos (a : List Int) (i : Nat) (h : 1 ≤ i) : pyGet a ((i : Int) - 1) = a.getD (i - 1) 0 := by
  unfold pyGet
  rw [if_neg (by omega), show ((i : Int) - 1).toNat = i - 1 by omega]
  rfl

end PyLean.Datetime.Zone

namespace PyLean.Datetime.Zone

theorem fromutcPy_after (zp : PyZone) (ts y : Int) (n : Nat) (t : TTI) (hn : zp.transUtc.length = n)
    (hn0 : n ≠ 0) (hne : zp.transUtc ≠ []) (hlen : zp.ttinfos.length = n)
    (h1 : ¬ ts < zp.transUtc.getD 0 0) (h2 : ts > zp.transUtc.getD (n - 1) 0)
    (h1' : n > 1 → ts ≥ zp.transUtc.getD 1 0)
    (ha : zp.tzAfter = .tti t) (hI : bisectRightPy zp.transUtc ts = n) :
    fromutcCorePy zp ts (.ok y) =
      if n > 1 then .ok (zp.ttinfos.getD (n - 1) default,
        decide ((zp.ttinfos.getD (n - 2) default).utcoff - (zp.ttinfos.getD (n - 1) default).utcoff >
          ts - zp.transUtc.getD (n - 1) 0))
      else .ok (t, decide ((zp.ttiBefore.getD default).utcoff - t.utcoff > ts - zp.transUtc.getD (n - 1) 0)) := by
  unfold fromutcCorePy
  simp only [hn, ha, getLast_getD _ hne, hI]
  rw [if_neg (by omega)]
  simp only [h2, or_true, true_and, Option.isSome_none, Bool.false_eq_true, ite_false, hn0, ite_true,
    pyGet_pos _ _ (Nat.one_le_iff_ne_zero.mpr hn0)]
  by_cases hn1 : n > 1
  · rw [if_pos ⟨hn1, h1' hn1⟩, if_pos hn1, pySlice_two _ _ (by omega) (by omega)]
    rfl
  · rw [if_neg (fun e => hn1 e.1), if_neg hn1]
    rfl

theorem fromutcC_after (zc : CZone) (ts y : Int) (n : Nat) (hn : zc.transUtc.length = n) (hn0 : n ≠ 0)
    (h1 : ¬ ts < zc.transUtc.getD 0 0) (h2 : ts > zc.transUtc.getD (n - 1) 0)
    (hso : zc.rule.stdOnly = true)
    (hp : -2 ^ 40 ≤ (if n = 1 then zc.ttiBefore.getD default else zc.ttinfos.getD (n - 2) default).utcoff ∧
      (if n = 1 then zc.ttiBefore.getD default else zc.ttinfos.getD (n - 2) default).utcoff ≤ 2 ^ 40)
    (hs : -2 ^ 40 ≤ zc.rule.std.utcoff ∧ zc.rule.std.utcoff ≤ 2 ^ 40)
    (ha : -2 ^ 62 ≤ zc.transUtc.getD (n - 1) 0 ∧ zc.transUtc.getD (n - 1) 0 ≤ 2 ^ 62) :
    fromutcCoreC zc ts y = (zc.rule.std,
      decide ((if n = 1 then zc.ttiBefore.getD default else zc.ttinfos.getD (n - 2) default).utcoff -
        zc.rule.std.utcoff > ts - zc.transUtc.getD (n - 1) 0)) := by
  unfold fromutcCoreC
  simp only [hn, CRule.findFromutc, hso, ite_true]
  rw [if_neg (by omega), if_pos (Or.inr h2)]
  simp only [ne_eq, hn0, not_false_eq_true, ite_true]
  generalize (if n = 1 then zc.ttiBefore.getD default else zc.ttinfos.getD (n - 2) default) = p at hp ⊢
  rw [wrap64_id (p.utcoff - zc.rule.std.utcoff) (by omega) (by omega),
    wrap64_id (zc.transUtc.getD (n - 1) 0 + (p.utcoff - zc.rule.std.utcoff)) (by omega) (by omega)]
  by_cases hf : p.utcoff - zc.rule.std.utcoff > 0 ∧
      ts < zc.transUtc.getD (n - 1) 0 + (p.utcoff - zc.rule.std.utcoff)
  · rw [if_pos hf]; simp only [Prod.mk.injEq, true_and]; symm; simp only [decide_eq_true_eq]; omega
  · rw [if_neg hf]; simp only [Prod.mk.injEq, true_and]; symm; simp only [decide_eq_false_iff_not]; omega

theorem fromutcC_in (zc : CZone) (ts y : Int) (n idx : Nat) (hn : zc.transUtc.length = n) (hn0 : n ≠ 0)
    (h1 : ¬ ts < zc.transUtc.getD 0 0) (h2 : ¬ ts > zc.transUtc.getD (n - 1) 0)
    (hI : bisectC ts zc.transUtc = idx) (_hi1 : 1 ≤ idx) :
    fromutcCoreC zc ts y =
      (let (ttiPrev, tti) := if idx ≥ 2 then (zc.ttinfos.getD (idx - 2) default, zc.ttinfos.getD (idx - 1) default)
        else (zc.ttiBefore.getD default, zc.ttinfos.getD 0 default)
      (tti, decide (wrap64 (ttiPrev.utcoff - tti.utcoff) > wrap64 (ts - zc.transUtc.getD (idx - 1) 0)))) := by
  unfold fromutcCoreC
  simp only [hn, hI]
  rw [if_neg (by omega), if_neg (by omega)]

theorem fromutcPy_in (zp : PyZone) (ts y : Int) (n idx : Nat) (hn : zp.transUtc.length = n) (hn0 : n ≠ 0)
    (hne : zp.transUtc ≠ []) (hlen : zp.ttinfos.length = n)
    (h1 : ¬ ts < zp.transUtc.getD 0 0) (h2 : ¬ ts > zp.transUtc.getD (n - 1) 0)
    (hI : bisectRightPy zp.transUtc ts = idx) (hi1 : 1 ≤ idx) (hin : idx ≤ n)
    (hc2 : (n > 1 ∧ ts ≥ zp.transUtc.getD 1 0) ↔ idx ≥ 2) :
    fromutcCorePy zp ts (.ok y) =
      .ok (let (ttiPrev, tti) := if idx ≥ 2 then (zp.ttinfos.getD (idx - 2) default, zp.ttinfos.getD (idx - 1) default)
        else (zp.ttiBefore.getD default, zp.ttinfos.getD 0 default)
      (tti, decide (ttiPrev.utcoff - tti.utcoff > ts - zp.transUtc.getD (idx - 1) 0))) := by
  unfold fromutcCorePy
  simp only [hn, getLast_getD _ hne, hI]
  rw [if_neg (by omega)]
  simp only [h2, or_false, hn0, false_and, ite_false, pyGet_pos _ _ hi1]
  by_cases hi2 : idx ≥ 2
  · rw [if_pos (hc2.mpr hi2), if_pos hi2, pySlice_two _ _ hi2 (by omega)]
    rfl
  · rw [if_neg (fun e => hi2 (hc2.mp e)), if_neg hi2]
    rfl

theorem fromutc_core_sorted (zp : PyZone) (zc : CZone) (hc : Corr zp zc)
    (hlen : zp.ttinfos.length = zp.transUtc.length) (hs : SortedL zp.transUtc)
    (hb : ∀ t ∈ zp.transUtc, -2 ^ 62 ≤ t ∧ t ≤ 2 ^ 62)
    (hu : ∀ t ∈ zp.ttinfos, -2 ^ 40 ≤ t.utcoff ∧ t.utcoff ≤ 2 ^ 40)
    (hbe : -2 ^ 40 ≤ (zp.ttiBefore.getD default).utcoff ∧ (zp.ttiBefore.getD default).utcoff ≤ 2 ^ 40)
    (hn : zp.transUtc ≠ []) (ts y : Int) (hts : -2 ^ 50 ≤ ts ∧ ts ≤ 2 ^ 50)
    (hcase : ts ≤ zp.transUtc.getLast?.getD 0 ∨
      zp.tzAfter = .tti (zp.ttinfos.getLast?.getD default)) :
    fromutcCorePy zp ts (.ok y) = .ok (fromutcCoreC zc ts y) := by
  have hn0 : zp.transUtc.length ≠ 0 := by simpa using hn
  have hnt : zp.ttinfos ≠ [] := by intro e; rw [e] at hlen; simp at hlen; omega
  rw [getLast_getD _ hn, getLast_getD_tti _ hnt, hlen] at hcase
  have hbn := int_bound zp.transUtc hb
  have htt := tti_bound zp.ttinfos hu
  have spec := bisect_spec zp.transUtc ts hs (zp.transUtc.length + 1) 0 zp.transUtc.length
    (Nat.zero_le _) (Nat.le_refl _) (by omega) (fun j hj => absurd hj (Nat.not_lt_zero _))
    (fun j hj hj2 => absurd hj2 (by omega))
  obtain ⟨idx, hI⟩ : ∃ i, bisectRightPy zp.transUtc ts = i := ⟨_, rfl⟩
  have hIc : bisectC ts zc.transUtc = idx := by rw [hc.trans, bisect_eq, hI]
  simp only [bisectRightPy] at hI
  rw [hI] at spec
  obtain ⟨hidx, hle, hgt⟩ := spec
  have hctl : zc.transUtc.length = zp.transUtc.length := by rw [hc.trans]
  by_cases h1 : ts < zp.transUtc.getD 0 0
  · unfold fromutcCorePy fromutcCoreC
    rw [hc.trans, hc.before, if_pos ⟨by omega, h1⟩, if_pos ⟨by omega, h1⟩]
    rfl
  · have hi1 : 1 ≤ idx := by
      rcases Nat.lt_or_ge idx 1 with e | e
      · have := hgt 0 (by omega) (by omega); omega
      · exact e
    by_cases h2 : ts > zp.transUtc.getD (zp.transUtc.length - 1) 0
    · have hta : zp.tzAfter = .tti (zp.ttinfos.getD (zp.transUtc.length - 1) default) := by
        rcases hcase with e | e
        · omega
        · exact e
      have hin : idx = zp.transUtc.length := by
        rcases Nat.lt_or_ge idx zp.transUtc.length with e | e
        · have := hgt (zp.transUtc.length - 1) (by omega) (by omega); omega
        · omega
      have ha := hc.after
      rw [hta] at ha
      obtain ⟨⟨hso, hstd⟩, -⟩ := ha
      have h1' : zp.transUtc.length > 1 → ts ≥ zp.transUtc.getD 1 0 := fun hn1 =>
        hle 1 (by omega)
      rw [fromutcPy_after zp ts y _ _ rfl hn0 hn hlen h1 h2 h1' hta (by simp only [bisectRightPy]; omega)]
      have hpb : -2 ^ 40 ≤ (if zp.transUtc.length = 1 then zc.ttiBefore.getD default
          else zc.ttinfos.getD (zp.transUtc.length - 2) default).utcoff ∧
          (if zp.transUtc.length = 1 then zc.ttiBefore.getD default
          else zc.ttinfos.getD (zp.transUtc.length - 2) default).utcoff ≤ 2 ^ 40 := by
        rw [hc.before, hc.ttinfos]; split
        · exact hbe
        · exact htt _
      rw [fromutcC_after zc ts y _ hctl hn0 (by rw [hc.trans]; exact h1) (by rw [hc.trans]; exact h2) hso
        hpb (by rw [hstd]; exact htt _) (by rw [hc.trans]; exact hbn _)]
      rw [hstd, hc.before, hc.ttinfos, hc.trans]
      by_cases hn1 : zp.transUtc.length > 1
      · rw [if_pos hn1, if_neg (by omega)]
      · rw [if_neg hn1, if_pos (by omega)]
    · have hc2 : (zp.transUtc.length > 1 ∧ ts ≥ zp.transUtc.getD 1 0) ↔ idx ≥ 2 := by
        constructor
        · intro ⟨e1, e2⟩
          rcases Nat.lt_or_ge idx 2 with e | e
          · have := hgt 1 (by omega) e1; omega
          · exact e
        · intro e; exact ⟨by omega, hle 1 (by omega)⟩
      rw [fromutcPy_in zp ts y _ idx rfl hn0 hn hlen h1 h2 (by simp only [bisectRightPy]; exact hI) hi1 hidx hc2,
        fromutcC_in zc ts y _ idx hctl hn0 (by rw [hc.trans]; exact h1) (by rw [hc.trans]; exact h2) hIc hi1]
      rw [hc.ttinfos, hc.before, hc.trans]
      have hbl := hbn (idx - 1)
      by_cases hi2 : idx ≥ 2
      · simp only [if_pos hi2]
        have := htt (idx - 2); have := htt (idx - 1)
        rw [wrap64_id _ (by omega) (by omega), wrap64_id _ (by omega) (by omega)]
      · simp only [if_neg hi2]
        have := htt 0
        rw [wrap64_id _ (by omega) (by omega), wrap64_id _ (by omega) (by omega)]

/-- `fromutc` agrees between the twins for every plain `datetime` on a zone whose transitions
are in ascending order (RFC 9636 §3.2), whose offsets are TZif-sized and whose transition times
keep `int64_t` sums exact, wherever the instant is not after the last transition, or after it
when the rule there is the last transition's own `_ttinfo` (the two refuted cases). -/
def FromutcTwinsSorted : Prop :=
  ∀ (zp : PyZone) (zc : CZone), Corr zp zc → zp.ttinfos.length = zp.transUtc.length →
    SortedL zp.transUtc → (∀ t ∈ zp.transUtc, -2 ^ 62 ≤ t ∧ t ≤ 2 ^ 62) →
    (∀ t ∈ zp.ttinfos, -2 ^ 40 ≤ t.utcoff ∧ t.utcoff ≤ 2 ^ 40) →
    (-2 ^ 40 ≤ (zp.ttiBefore.getD default).utcoff ∧ (zp.ttiBefore.getD default).utcoff ≤ 2 ^ 40) →
    zp.transUtc ≠ [] →
    ∀ (y m d h mi s : Int), ValidDT y m d h mi s 0 →
      ((ymd2ord y m d - EPOCHORDINAL) * 86400 + h * 3600 + mi * 60 + s ≤ zp.transUtc.getLast?.getD 0 ∨
        zp.tzAfter = .tti (zp.ttinfos.getLast?.getD default)) →
      fromutcC zc (DTObj.ofFields y m d h mi s 0) true = fromutcPy zp (DTObj.ofFields y m d h mi s 0) true

theorem fromutcTwinsSorted_proven : FromutcTwinsSorted := by
  intro zp zc hc hlen hs hb hu hbe hn y m d h mi s hv hcase
  have hts := localTs_eq y m d h mi s 0 hv
  obtain ⟨hy1, hy2, hm1, hm2, hd1, hd2, hh1, hh2, hmi1, hmi2, hs1, hs2, -⟩ := hv
  have ht := month_tables m hm1 hm2
  have hdby := daysBeforeYear_bounds y hy1 hy2
  have hdm : daysInMonth y m ≤ 31 := by unfold daysInMonth; split <;> omega
  have hl : 0 ≤ (if m > 2 ∧ isLeap y = true then (1 : Int) else 0) ∧
      (if m > 2 ∧ isLeap y = true then (1 : Int) else 0) ≤ 1 := by constructor <;> split <;> omega
  have htsb : -2 ^ 50 ≤ (ymd2ord y m d - EPOCHORDINAL) * 86400 + h * 3600 + mi * 60 + s ∧
      (ymd2ord y m d - EPOCHORDINAL) * 86400 + h * 3600 + mi * 60 + s ≤ 2 ^ 50 := by
    rw [ymd2ord_eq]; unfold EPOCHORDINAL; omega
  unfold fromutcC fromutcPy
  rw [hts]
  simp only [getLocalTsPy, DTObj.ofFields, bind, Except.bind, pure, Except.pure, Bool.not_true,
    Bool.false_eq_true, ite_false]
  rw [fromutc_core_sorted zp zc hc hlen hs hb hu hbe hn _ y htsb hcase]

end PyLean.Datetime.Zone
