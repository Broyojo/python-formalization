import PyLean.Datetime.Spec

/-!
ISO 8601 parsing (`fromisoformat`) in CPython 3.14.7: properties refuted by
concrete strings. Each refutation is evaluated on the models of both twins.
-/

namespace PyLean.Datetime

open PyLean

/-- `date.fromisoformat`: C and Python agree on the result and the exception
class for every string. -/
def DateFromisoTwins : Prop :=
  ∀ s : List Char, SameOutcome (dateFromIsoPy s) (dateFromIsoC s)

/-- `_pydatetime.date.fromisoformat('2020-+1-01')` is `date(2020, 1, 1)`:
`int('+1')` accepts the sign. The C parser rejects the string. -/
theorem dateFromisoTwins_refuted : ¬DateFromisoTwins := by
  intro h
  have h1 := h "2020-+1-01".toList
  have e1 : dateFromIsoPy "2020-+1-01".toList = .ok (2020, 1, 1) := by decide
  have e2 : dateFromIsoC "2020-+1-01".toList = .error (.valueError "~Invalid isoformat string") := by decide
  rw [e1, e2] at h1
  exact h1

/-- `time.fromisoformat`: C and Python agree on the result and the exception
class for every string. -/
def TimeFromisoTwins : Prop :=
  ∀ s : List Char, SameOutcome (timeFromIsoPy s) (timeFromIsoC s)

/-- C `time.fromisoformat('12345678')` is `time(12, 34, 56, 780000)`: the two
digits after `HHMMSS` are read as a fraction without a decimal mark. Python
rejects the string. -/
theorem timeFromisoTwins_refuted : ¬TimeFromisoTwins := by
  intro h
  have h1 := h "12345678".toList
  have e1 : timeFromIsoPy "12345678".toList = .error (.valueError "~Invalid isoformat string") := by decide
  have e2 : timeFromIsoC "12345678".toList = .ok ⟨12, 34, 56, 780000, none⟩ := by decide
  rw [e1, e2] at h1
  exact h1

/-- `datetime.fromisoformat`: C and Python agree on the result and the
exception class for every string. -/
def DatetimeFromisoTwins : Prop :=
  ∀ s : List Char, SameOutcome (datetimeFromIsoPy s) (datetimeFromIsoC s)

/-- C `datetime.fromisoformat('2020-01-01T12:00Z\x00junk')` returns
`12:00 UTC`: after `Z` the C parser only checks that the next byte is NUL, so an
embedded NUL hides the rest of the string. Python rejects the string. -/
theorem datetimeFromisoTwins_refuted : ¬DatetimeFromisoTwins := by
  intro h
  have h1 := h "2020-01-01T12:00Z\x00junk".toList
  have e1 : datetimeFromIsoPy "2020-01-01T12:00Z\x00junk".toList =
      .error (.valueError "~Invalid isoformat string") := by decide
  have e2 : datetimeFromIsoC "2020-01-01T12:00Z\x00junk".toList =
      .ok ⟨2020, 1, 1, ⟨12, 0, 0, 0, some 0⟩⟩ := by decide
  rw [e1, e2] at h1
  exact h1

/-- A `date.isoformat()` string followed by one separator character and no
time is not a valid `datetime` string: both twins raise `ValueError`. -/
def DatetimeFromisoBareSeparator : Prop :=
  ∀ (y m d : Int) (c : Char), ValidDate y m d →
    (datetimeFromIsoPy (dateIsoformat y m d ++ [c])).raises "ValueError" ∧
    (datetimeFromIsoC (dateIsoformat y m d ++ [c])).raises "ValueError"

/-- `_pydatetime.datetime.fromisoformat('2009-04-19T')` is midnight: an empty
time part after the separator is skipped by `if tstr:`. -/
theorem datetimeFromisoBareSeparator_refuted : ¬DatetimeFromisoBareSeparator := by
  intro h
  have h1 := (h 2009 4 19 'T' (by decide)).1
  have e1 : datetimeFromIsoPy (dateIsoformat 2009 4 19 ++ ['T']) = .ok ⟨2009, 4, 19, ⟨0, 0, 0, 0, none⟩⟩ := by
    decide
  rw [e1] at h1
  obtain ⟨_, h2, _⟩ := h1
  cases h2

/-- `24:00` is midnight at the end of the day, so `D + 'T24:00'` can only be
accepted when the date `D` is: in both twins, if
`datetime.fromisoformat(D + 'T24:00')` returns a value, so does
`datetime.fromisoformat(D)`. -/
def DatetimeFromisoMidnightNeedsValidDate : Prop :=
  ∀ D : List Char,
    ((datetimeFromIsoPy (D ++ "T24:00".toList)).isOk → (datetimeFromIsoPy D).isOk) ∧
    ((datetimeFromIsoC (D ++ "T24:00".toList)).isOk → (datetimeFromIsoC D).isOk)

/-- `datetime.fromisoformat('2020-01-00T24:00')` is `2020-01-01 00:00` in both
twins, while `datetime.fromisoformat('2020-01-00')` raises (day 0). The rollover
checks `day <= days_in_month` but not `day >= 1`. -/
theorem datetimeFromisoMidnightNeedsValidDate_refuted : ¬DatetimeFromisoMidnightNeedsValidDate := by
  intro h
  have h1 := (h "2020-01-00".toList).1
  have e1 : datetimeFromIsoPy ("2020-01-00".toList ++ "T24:00".toList) =
      .ok ⟨2020, 1, 1, ⟨0, 0, 0, 0, none⟩⟩ := by decide
  have e2 : datetimeFromIsoPy "2020-01-00".toList =
      .error (.valueError "day 0 must be in range 1..31 for month 1 in year 2020") := by decide
  have e3 : datetimeFromIsoC ("2020-01-00".toList ++ "T24:00".toList) =
      .ok ⟨2020, 1, 1, ⟨0, 0, 0, 0, none⟩⟩ := by decide
  have e4 : datetimeFromIsoC "0000-12-31T24:00".toList = .ok ⟨1, 1, 1, ⟨0, 0, 0, 0, none⟩⟩ := by decide
  rw [e1, e2] at h1
  exact absurd (h1 rfl) (by decide)

/-- A 10-character `date.fromisoformat` argument is accepted only in the
extended format `YYYY-MM-DD` or `YYYY-Www-D`, i.e. with `-` at index 4: in both
twins, `date.fromisoformat(s)` returning a value for `len(s) == 10` implies
`s[4] == '-'`. -/
def DateFromisoTenChars : Prop :=
  ∀ s : List Char, s.length = 10 →
    ((dateFromIsoPy s).isOk → s[4]? = some '-') ∧ ((dateFromIsoC s).isOk → s[4]? = some '-')

/-- `date.fromisoformat('2020010112')` is `date(2020, 1, 1)` in both twins:
the basic-format parser reads 8 characters and ignores the last two. -/
theorem dateFromisoTenChars_refuted : ¬DateFromisoTenChars := by
  intro h
  have h1 := (h "2020010112".toList (by decide)).1
  have e1 : dateFromIsoPy "2020010112".toList = .ok (2020, 1, 1) := by decide
  have e2 : dateFromIsoC "2020010112".toList = .ok (2020, 1, 1) := by decide
  rw [e1] at h1
  exact absurd (h1 rfl) (by decide)

end PyLean.Datetime
