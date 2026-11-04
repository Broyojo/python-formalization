import PyLean.BytesObj.Bytes.BasicProps5

/-!
What `PyBytes_FromFormat` writes for each conversion: `bytes_fromformat`, Objects/bytesobject.c:187-358,
through `PyBytes_FromFormatV`, :361-377.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

set_option linter.unusedSimpArgs false

/-- `sprintf("%d")` is the decimal text of the value. -/
theorem cDecimal_eq (v : Int) : cDecimal v = asc (toString v) := by
  cases v with
  | ofNat n =>
    have h : ¬ ((Int.ofNat n) < 0) := Int.not_lt.mpr (Int.ofNat_nonneg n)
    simp [cDecimal, h, digitsOf, asc, toString, Int.repr, Nat.repr]
  | negSucc n =>
    have h : (Int.negSucc n) < 0 := Int.negSucc_lt_zero n
    simp [cDecimal, h, digitsOf, asc, toString, Int.repr, Nat.repr]

/-- The conversions of `PyBytes_FromFormat` on the LP64 ABI the pod runs (`int` 32 bits, `long` and
`Py_ssize_t` 64): `%d` and `%i` print the argument as an `int`, `%u` as an `unsigned int`, `%ld` and `%zd`
as 64-bit signed and `%lu` and `%zu` as unsigned, `%x` the `int` in hex, `%c` the byte for a value in
`[0, 255]` and the `OverflowError` otherwise (:258-268), `%s` the C string up to its NUL and `%.3s` at
most 3 of its bytes (:315-326), `%p` `0x` and the hex digits, and glibc's `(nil)` with `0x` for NULL
(:328-340), `%%` a percent sign; a width is skipped (:224-226), the arguments are taken in order, and an
invalid conversion copies the rest of the format unchanged (:345-348). -/
def FromFormatConv : Prop :=
  (∀ v : Int, bytesFromFormat (asc "%d") [.int v] = .ok (asc (toString (wrapInt v)))) ∧
  (∀ v : Int, bytesFromFormat (asc "%i") [.int v] = .ok (asc (toString (wrapInt v)))) ∧
  (∀ v : Int, bytesFromFormat (asc "%u") [.int v] = .ok (asc (toString (v % 2 ^ 32)))) ∧
  (∀ v : Int, bytesFromFormat (asc "%ld") [.int v] = .ok (asc (toString (RangeSlice.wrap v)))) ∧
  (∀ v : Int, bytesFromFormat (asc "%zd") [.int v] = .ok (asc (toString (RangeSlice.wrap v)))) ∧
  (∀ v : Int, bytesFromFormat (asc "%lu") [.int v] = .ok (asc (toString (v % 2 ^ 64)))) ∧
  (∀ v : Int, bytesFromFormat (asc "%zu") [.int v] = .ok (asc (toString (v % 2 ^ 64)))) ∧
  (∀ v : Int, bytesFromFormat (asc "%x") [.int v] = .ok (digitsBase 16 (v % 2 ^ 32).toNat)) ∧
  (∀ v : Int, bytesFromFormat (asc "%5d") [.int v] = .ok (asc (toString (wrapInt v)))) ∧
  (∀ a b : Int, bytesFromFormat (asc "%d%d") [.int a, .int b] =
    .ok (asc (toString (wrapInt a)) ++ asc (toString (wrapInt b)))) ∧
  (∀ v : Int, 0 ≤ v → v ≤ 255 → bytesFromFormat (asc "%c") [.int v] = .ok [v.toNat]) ∧
  (∀ v : Int, (v < 0 ∨ v > 255) → bytesFromFormat (asc "%c") [.int v] =
    .error (.overflowError "PyBytes_FromFormatV(): %c format expects an integer in range [0; 255]")) ∧
  (∀ s : Seq, 0 ∉ s → bytesFromFormat (asc "%s") [.str s] = .ok s) ∧
  (∀ s : Seq, bytesFromFormat (asc "%.3s") [.str s] = .ok ((s.takeWhile (· != 0)).take 3)) ∧
  (∀ p : Nat, p ≠ 0 → bytesFromFormat (asc "%p") [.ptr p] = .ok (asc "0x" ++ digitsBase 16 p)) ∧
  (bytesFromFormat (asc "%p") [.ptr 0] = .ok (asc "0x(nil)")) ∧
  (bytesFromFormat (asc "%%") [] = .ok (asc "%")) ∧
  (∀ args : List CArg, bytesFromFormat (asc "ab%q%d") args = .ok (asc "ab%q%d"))

theorem asc_ff0 : asc "%d" = [37, 100] := by decide
theorem asc_ff1 : asc "%i" = [37, 105] := by decide
theorem asc_ff2 : asc "%u" = [37, 117] := by decide
theorem asc_ff3 : asc "%ld" = [37, 108, 100] := by decide
theorem asc_ff4 : asc "%zd" = [37, 122, 100] := by decide
theorem asc_ff5 : asc "%lu" = [37, 108, 117] := by decide
theorem asc_ff6 : asc "%zu" = [37, 122, 117] := by decide
theorem asc_ff7 : asc "%x" = [37, 120] := by decide
theorem asc_ff8 : asc "%5d" = [37, 53, 100] := by decide
theorem asc_ff9 : asc "%d%d" = [37, 100, 37, 100] := by decide
theorem asc_ff10 : asc "%c" = [37, 99] := by decide
theorem asc_ff11 : asc "%s" = [37, 115] := by decide
theorem asc_ff12 : asc "%.3s" = [37, 46, 51, 115] := by decide
theorem asc_ff13 : asc "%p" = [37, 112] := by decide
theorem asc_ff14 : asc "%%" = [37, 37] := by decide
theorem asc_ff15 : asc "ab%q%d" = [97, 98, 37, 113, 37, 100] := by decide
theorem asc_ff16 : asc "0x(nil)" = [48, 120, 40, 110, 105, 108, 41] := by decide
theorem asc_ff17 : asc "0x" = [48, 120] := by decide
theorem asc_ff18 : asc "%" = [37] := by decide

theorem takeWhile_nz' (s : Seq) (h : 0 ∉ s) : s.takeWhile (· != 0) = s := by
  induction s with
  | nil => rfl
  | cons c cs ih =>
    have hc : c ≠ 0 := fun e => h (by simp [e])
    have hcs : 0 ∉ cs := fun e => h (by simp [e])
    simp [hc, ih hcs]

/-- Run `fromFormatLoop` on a concrete format. -/
macro "ff_run" : tactic => `(tactic| (
  simp only [bytesFromFormat, List.length_cons, List.length_nil]
  repeat (rw [fromFormatLoop]; simp [cAt, skipDigits, skipToConv, precDigits, isDigitC, isAlphaC,
    isUpperC, isLowerC])))

theorem fromFormatConv_proven : FromFormatConv := by
  have hd : ∀ v, cDecimal v = asc (toString v) := cDecimal_eq
  unfold FromFormatConv
  simp only [asc_ff0, asc_ff1, asc_ff2, asc_ff3, asc_ff4, asc_ff5, asc_ff6, asc_ff7, asc_ff8, asc_ff9, asc_ff10, asc_ff11, asc_ff12, asc_ff13, asc_ff14, asc_ff15, asc_ff16, asc_ff17, asc_ff18]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v; ff_run; simp [hd]
  · intro v; ff_run; simp [hd]
  · intro v; ff_run; simp [hd]
  · intro v; ff_run; simp [hd]
  · intro v; ff_run; simp [hd]
  · intro v; ff_run; simp [hd]
  · intro v; ff_run; simp [hd]
  · intro v; ff_run
  · intro v; ff_run; simp [hd]
  · intro a b; ff_run; simp [hd]
  · intro v h1 h2
    ff_run
    omega
  · intro v h
    ff_run
    omega
  · intro s h
    ff_run
    simp [cStringPrec, takeWhile_nz' s h]
  · intro s
    ff_run
    simp [cStringPrec, precDigits, isDigitC, RangeSlice.wrap, RangeSlice.longMax, RangeSlice.two64]
  · intro p hp
    ff_run
    simp [hp, asc_ff17]
  · ff_run
    simp [asc_ff16]
  · ff_run
  · intro args
    ff_run

end PyLean.BytesObj.Bytes
