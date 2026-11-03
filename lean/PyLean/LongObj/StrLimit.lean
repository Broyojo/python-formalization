import PyLean.LongObj.PylongInt

/-!
`str(int)` and the integer string conversion limit, `Objects/longobject.c`
(CPython 3.15.2): `long_to_decimal_string`, `long_to_decimal_string_internal` and
`pylong_int_to_decimal_string`.

The exact behaviour is `longToDecimalString_eq` (PylongStr.lean). On the `_pylong`
path (`size_a > 1000`, longobject.c:2138-2145) only the rough pre-check of :2125-2135
guards the limit; the exact check of :2207-2217 is never reached. For a limit of 9000
or more the pre-check lets through values with more digits than the limit, so the
documented promise is refuted here, and proven for every limit below 9000.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt

/-! ## The output form -/

/-- `decStr v` is an optional `-` followed by decimal digits, at least one, with no
leading zero unless `v = 0`. So there is no `+`, no `_` and no padding. -/
theorem decStr_canonical (v : Int) : ∃ ds, decStr v = (if v < 0 then ['-'] else []) ++ ds ∧
    ds ≠ [] ∧ (∀ c ∈ ds, c.isDigit = true) ∧ (v ≠ 0 → ds.head? ≠ some '0') := by
  refine ⟨Nat.toDigits 10 v.natAbs, rfl, Nat.toDigits_ne_nil,
    fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc, ?_⟩
  intro hv
  obtain ⟨c, t, e, hc⟩ := toDigits_head (m := v.natAbs) (Int.natAbs_pos.2 hv)
  rw [e]
  simpa using hc

/-! ## `str(int)`: the whole behaviour -/

/-- `str(v)` for every `int` `v` and every limit that `sys.set_int_max_str_digits`
accepts (`ValidLimit`, a type invariant of the interpreter state). Up to 1000 digits
of `2**30` it raises the limit `ValueError` (with the exact message of
`_MAX_STR_DIGITS_ERROR_FMT_TO_STR`, longobject.c:33) exactly when a non-zero limit is
below the decimal digit count; above 1000 digits only the pre-check decides. Whenever
it returns, it returns `decStr v`, which the second conjunct pins as canonical
decimal: an optional `-`, then digits with no leading zero, no `+` and no `_`. -/
def StrIntExact : Prop :=
  (∀ (lim : Nat) (v : Int), ValidLimit lim →
    longToDecimalString lim (Long.ofInt v) =
      if sizeOf' v ≤ 1000 then
        if lim > 0 ∧ numDigits v > lim then .error (.valueError (limitToStrMsg lim))
        else .ok (decStr v)
      else
        if lim > 0 ∧ lim / 90 ≤ (sizeOf' v - 11) / 10 then
          .error (.valueError (limitToStrMsg lim))
        else .ok (decStr v)) ∧
  ∀ v : Int, ∃ ds, decStr v = (if v < 0 then ['-'] else []) ++ ds ∧ ds ≠ [] ∧
    (∀ c ∈ ds, c.isDigit = true) ∧ (v ≠ 0 → ds.head? ≠ some '0')

theorem strIntExact_proven : StrIntExact :=
  ⟨fun _ v hlim => longToDecimalString_eq hlim v, decStr_canonical⟩

/-- `pylong_int_to_decimal_string` (longobject.c:2026-2088) passes an import failure
(:2033-2036) and an exception from `_pylong.int_to_decimal_string` (:2037-2040)
through, rejects a non-`str` result with the TypeError of :2041-2045, and otherwise
returns the characters of the `str`. All inputs: the import and the call are
arbitrary, since `_pylong` can be replaced through `sys.modules`. -/
def PylongToDecimalPaths : Prop :=
  ∀ (imp : Py Unit) (call : Long → Py PylongStrRes) (x : Long),
    (∀ e, imp = .error e → pylongIntToDecimalString imp call x = .error e) ∧
    (imp = .ok () → ∀ e, call x = .error e → pylongIntToDecimalString imp call x = .error e) ∧
    (imp = .ok () → call x = .ok .other → pylongIntToDecimalString imp call x =
      .error (.typeError "_pylong.int_to_decimal_string did not return a str")) ∧
    (imp = .ok () → ∀ s, call x = .ok (.str s) → pylongIntToDecimalString imp call x = .ok s)

theorem pylongToDecimalPaths_proven : PylongToDecimalPaths := by
  intro imp call x
  refine ⟨fun e h => by subst h; rfl, fun h e hc => ?_, fun h hc => ?_, fun h s hc => ?_⟩ <;>
    (subst h; unfold pylongIntToDecimalString; rw [hc]; rfl)

/-! ## The documented limit -/

/-- Doc/builtins/stdtypes.rst:6820-6824: "The limit is applied to the number of digit
characters in the input or output string when a non-linear conversion algorithm would
be involved. Underscores and the sign are not counted towards the limit. When an
operation would exceed the limit, a :exc:`ValueError` is raised". `str(integer)` is
listed among the affected APIs (:6873). For every limit the setter accepts other than
`0` (at least 640, :6848-6849): `str(v)` raises exactly when the digit count without
the sign exceeds the limit, and otherwise returns the digits. -/
def StrDigitLimitExact : Prop :=
  ∀ (lim : Nat) (v : Int), strDigitsThreshold ≤ lim →
    longToDecimalString lim (Long.ofInt v) =
      if numDigits v > lim then .error (.valueError (limitToStrMsg lim)) else .ok (decStr v)

/-- With the limit at 10000, `str(10**10050)` returns all 10051 digits. `10**10050`
has 1113 digits of `2**30`, so it takes the `_pylong` path, and the pre-check needs
`10000 // 90 = 111 <= (1113 - 11) // 10 = 110`, which fails. -/
theorem strDigitLimitExact_refuted : ¬ StrDigitLimitExact := by
  intro h
  have hup : (10 : Nat) ^ 10050 < 2 ^ 33600 := by decide +kernel
  have hlo : (2 : Nat) ^ 33000 ≤ 10 ^ 10050 := by decide +kernel
  have hten : (10 : Nat) ^ 10000 ≤ 10 ^ 10050 := Nat.pow_le_pow_right (by decide) (by decide)
  have e := h 10000 ((10 ^ 10050 : Nat) : Int) (by decide)
  rw [longToDecimalString_eq (Or.inr (by decide))] at e
  generalize (10 : Nat) ^ 10050 = N at hup hlo hten e
  have hb1 : bitLength N ≤ 33600 := bitLength_le_of_lt' hup
  have hb2 : 33000 < bitLength N :=
    (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).1
      (Nat.lt_of_le_of_lt hlo (lt_two_pow_bitLength' N))
  have hs : sizeOf' (N : Int) = (bitLength N + 29) / 30 := rfl
  have hd : numDigits (N : Int) > 10000 := by
    apply Nat.lt_of_not_le
    intro hle
    have hlt : N < 10 ^ 10000 :=
      (Nat.length_toDigits_le_iff (b := 10) (by decide) (by decide)).1 hle
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt hten)
  have c1 : ¬ sizeOf' (N : Int) ≤ 1000 := by rw [hs]; omega
  have c2 : ¬ (10000 > 0 ∧ 10000 / 90 ≤ (sizeOf' (N : Int) - 11) / 10) := by rw [hs]; omega
  rw [if_neg c1, if_neg c2, if_pos hd] at e
  cases e

/-- The same promise holds for every limit from 640 up to 8999: there `lim // 90 <= 99`,
so the pre-check fires on every value that takes the `_pylong` path, and the exact
check of :2207-2217 handles the rest. -/
def StrDigitLimitBelow9000 : Prop :=
  ∀ (lim : Nat) (v : Int), strDigitsThreshold ≤ lim → lim < 9000 →
    longToDecimalString lim (Long.ofInt v) =
      if numDigits v > lim then .error (.valueError (limitToStrMsg lim)) else .ok (decStr v)

theorem strDigitLimitBelow9000_proven : StrDigitLimitBelow9000 := by
  intro lim v h1 h2
  have hthr : strDigitsThreshold = 640 := rfl
  rw [longToDecimalString_eq (Or.inr h1)]
  by_cases hs : sizeOf' v ≤ 1000
  · rw [if_pos hs]
    by_cases hd : numDigits v > lim
    · rw [if_pos ⟨by omega, hd⟩, if_pos hd]
    · rw [if_neg (fun h => hd h.2), if_neg hd]
  · rw [if_neg hs]
    have hp : lim > 0 ∧ lim / 90 ≤ (sizeOf' v - 11) / 10 := ⟨by omega, by omega⟩
    rw [if_pos hp, if_pos (precheck_digits (by omega) hp.1 hp.2)]

end PyLean.LongObj
