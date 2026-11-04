import PyLean.Datetime.TwinsProps

/-!
The timestamp conversion of `date.fromtimestamp` (C `date_fromtimestamp`,
Modules/_datetimemodule.c:3291-3306, through `_PyTime_ObjectToTime_t(obj, ROUND_FLOOR)`,
Python/pytime.c:484-520; Python's `_time.localtime(t)` runs the same conversion), CPython 3.15.2.
-/

namespace PyLean.Datetime

open PyLean

/-- `date.fromtimestamp(t)` in both twins, by the kind of `t`: an int outside the 64-bit
`time_t` range is `OverflowError: timestamp out of range for platform time_t` (an int inside
it is passed to `localtime` as is); a NaN is `ValueError: Invalid value NaN (not a number)`;
an infinity floors to itself and is `OverflowError`; a `str`, `bytes` or `tzinfo` is
`TypeError` (`PyFloat_AsDouble`), and `None` is `TypeError` in both (`DateFromtimestamp`).
The floor of a finite float and its range check are the open `datetime-timestamp-floor`. -/
def TimestampConversion : Prop :=
  ∀ k : Clock,
    (∀ n : Int, ¬(-2 ^ 63 ≤ n ∧ n < 2 ^ 63) →
      dateFromtimestampC k (.int n) = .error timeTOverflow ∧ dateFromtimestampPy k (.int n) = .error timeTOverflow) ∧
    (∀ n : Int, -2 ^ 63 ≤ n → n < 2 ^ 63 →
      dateFromtimestampC k (.int n) = (do let (y, m, d) ← k.localtime n; checkDateArgsC y m d; return (y, m, d))) ∧
    (∀ x : Binary64.F64, x.isNaN = true →
      dateFromtimestampC k (.float x) = .error (.valueError "Invalid value NaN (not a number)") ∧
      dateFromtimestampPy k (.float x) = .error (.valueError "Invalid value NaN (not a number)")) ∧
    (∀ x : Binary64.F64, x.isInf = true →
      dateFromtimestampC k (.float x) = .error timeTOverflow ∧ dateFromtimestampPy k (.float x) = .error timeTOverflow) ∧
    (∀ cs : List Nat, (dateFromtimestampC k (.str cs)).raises "TypeError" ∧ (dateFromtimestampPy k (.str cs)).raises "TypeError")

theorem timestampConversion_proven : TimestampConversion := by
  intro k
  refine ⟨fun n hn => ?_, fun n h1 h2 => ?_, fun x hx => ?_, fun x hx => ?_, fun cs => ?_⟩
  · have hn' : ¬(-9223372036854775808 ≤ n ∧ n < 9223372036854775808) := hn
    have e : objectToTimeT k (.int n) = .error timeTOverflow := by
      simp only [objectToTimeT, hn, hn', ite_false]
    refine ⟨?_, ?_⟩
    · unfold dateFromtimestampC; rw [e]; rfl
    · unfold dateFromtimestampPy timeLocaltime
      rw [if_neg (by intro h; cases h)]
      simp only [e, bind, Except.bind]
  · have hp : -9223372036854775808 ≤ n ∧ n < 9223372036854775808 := ⟨h1, h2⟩
    have e : objectToTimeT k (.int n) = .ok n := by
      simp only [objectToTimeT]; rw [if_pos ⟨h1, h2⟩]
    unfold dateFromtimestampC; rw [e]; rfl
  · simp [dateFromtimestampC, dateFromtimestampPy, timeLocaltime, objectToTimeT, hx, bind, Except.bind]
  · have hn : x.isNaN = false := by
      unfold Binary64.F64.isInf at hx; unfold Binary64.F64.isNaN; revert hx; cases x.isFinite <;> simp_all
    have hfin : x.isFinite = false := by
      unfold Binary64.F64.isInf at hx; unfold Binary64.F64.isFinite; revert hx; simp_all
    have hf : Binary64.F64.floor x = x := by
      unfold Binary64.F64.floor; simp [hn, hfin]
    have a1 : (Binary64.F64.ofInt (-9223372036854775808)).isNaN = false ∧
        (Binary64.F64.ofInt (-9223372036854775808)).isInf = false := by
      decide +kernel
    have a2 : (Binary64.F64.ofInt 9223372036854775808).isNaN = false ∧
        (Binary64.F64.ofInt 9223372036854775808).isInf = false := by
      decide +kernel
    have hc : (Binary64.F64.le (Binary64.F64.ofInt (-9223372036854775808)) x &&
        Binary64.F64.lt x (Binary64.F64.ofInt 9223372036854775808)) = false := by
      cases hs : x.sign
      · have : Binary64.F64.lt x (Binary64.F64.ofInt 9223372036854775808) = false := by
          unfold Binary64.F64.lt; simp [hn, hx, hs, a2.1]
        rw [this, Bool.and_false]
      · have : Binary64.F64.le (Binary64.F64.ofInt (-9223372036854775808)) x = false := by
          unfold Binary64.F64.le Binary64.F64.lt Binary64.F64.eq; simp [hn, hx, hs, a1.1, a1.2]
        rw [this, Bool.false_and]
    have e : objectToTimeT k (.float x) = .error timeTOverflow := by
      simp only [objectToTimeT]
      have e2 : (-2 ^ 63 : Int) = -9223372036854775808 := by decide
      have e3 : (2 ^ 63 : Int) = 9223372036854775808 := by decide
      rw [e2, e3]
      simp only [hn, hf, hc, Bool.false_eq_true, ite_false]
    have ep : timeLocaltime k (.float x) = .error timeTOverflow := by
      unfold timeLocaltime; simp only [e, bind, Except.bind]
    refine ⟨?_, ?_⟩
    · unfold dateFromtimestampC; rw [e]; rfl
    · unfold dateFromtimestampPy; rw [if_neg (by intro h; cases h), ep]; rfl
  · exact ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩

end PyLean.Datetime
