import PyLean.Pickle.Long

/-!
The protocol-0 `INT` and `LONG` opcodes: the C and Python unpicklers parse
the text argument (`load_int`/`load_long`, `Lib/pickle.py:1402-1430` and
`Modules/_pickle.c:5521-5700`) differently.

A line is `body ++ [\n]` with no newline in `body`: what both `readline`s
return when the line is complete.
-/

namespace PyLean.Pickle

open PyLean

/-- Accept/reject agreement: both return the same value, or both raise. -/
def SameOutcome {α : Type} : Py α → Py α → Prop
  | .ok a, .ok b => a = b
  | .error _, .error _ => True
  | _, _ => False

/-- For every line, the two `INT` parsers accept the same lines and return the
same value (an int, or a bool for the `I00`/`I01` spellings). Source: twin
agreement. -/
def IntLineTwins : Prop :=
  ∀ body : Bytes, nl ∉ body → SameOutcome (cLoadIntLine (body ++ [nl])) (pyLoadIntLine (body ++ [nl]))

/-- `I 1\n` was `True` in C through 3.14 (python/cpython#135241). `load_int` now
tests the spelling, as Python does: this line is the int 1 in both. -/
theorem cLoadInt_sp1 : cLoadIntLine [0x20, 0x31, nl] = .ok (.int 1) := by decide +kernel
theorem pyLoadInt_sp1 : pyLoadIntLine [0x20, 0x31, nl] = .ok (.int 1) := by decide +kernel

theorem cLoadInt_nul : cLoadIntLine [0x31, 0x32, 0, nl] = .ok (.int 12) := by decide +kernel
theorem pyLoadInt_nul_err : ∃ e, pyLoadIntLine [0x31, 0x32, 0, nl] = .error e := ⟨_, rfl⟩

/-- `I12\0\n`: C's strtol stops at the NUL that ends its C string and returns
12; `int(b'12\x00\n')` raises. python/cpython#126996 (open). -/
theorem intLineTwins_refuted : ¬ IntLineTwins := by
  intro h
  have := h [0x31, 0x32, 0] (by decide)
  simp only [List.cons_append, List.nil_append] at this
  rw [cLoadInt_nul] at this
  obtain ⟨e, he⟩ := pyLoadInt_nul_err
  rw [he] at this
  simp [SameOutcome] at this

/-- `IntLineTwins` without NUL bytes in the line. -/
def IntLineTwinsNoNul : Prop :=
  ∀ body : Bytes, nl ∉ body → (0 : UInt8) ∉ body →
    SameOutcome (cLoadIntLine (body ++ [nl])) (pyLoadIntLine (body ++ [nl]))

def zeros5000one : Bytes := List.replicate 5000 0x30 ++ [0x31]

set_option maxRecDepth 200000 in
theorem cLoadInt_limit : cLoadIntLine (zeros5000one ++ [nl]) = .ok (.int 1) := by decide +kernel
def isErr {α : Type} : Py α → Bool
  | .error _ => true
  | .ok _ => false

theorem exists_err_of_isErr {α : Type} {r : Py α} (h : isErr r = true) : ∃ e, r = .error e := by
  cases r with
  | error e => exact ⟨e, rfl⟩
  | ok _ => simp [isErr] at h

set_option maxRecDepth 200000 in
theorem pyLoadInt_limit_err : ∃ e, pyLoadIntLine (zeros5000one ++ [nl]) = .error e :=
  exists_err_of_isErr (by decide +kernel)

theorem zeros5000one_no_nl : nl ∉ zeros5000one := by
  simp only [zeros5000one, List.mem_append, List.mem_replicate, List.mem_singleton]; decide
theorem zeros5000one_no_nul : (0 : UInt8) ∉ zeros5000one := by
  simp only [zeros5000one, List.mem_append, List.mem_replicate, List.mem_singleton]; decide

set_option maxRecDepth 200000 in
/-- `I` + 5000 zeros + `1`: C's strtol fast path returns 1 without the
4300-digit limit of `int()`, which the Python twin enforces. -/
theorem intLineTwinsNoNul_refuted : ¬ IntLineTwinsNoNul := by
  intro h
  have := h zeros5000one zeros5000one_no_nl zeros5000one_no_nul
  rw [cLoadInt_limit] at this
  obtain ⟨e, he⟩ := pyLoadInt_limit_err
  rw [he] at this
  simp [SameOutcome] at this

/-- For every `LONG` line, the two parsers agree on acceptance and value. -/
def LongLineTwins : Prop :=
  ∀ body : Bytes, nl ∉ body → SameOutcome (cLoadLongLine (body ++ [nl])) (pyLoadLongLine (body ++ [nl]))

theorem cLoadLong_nul : cLoadLongLine [0x35, 0, nl] = .ok 5 := by decide +kernel
theorem pyLoadLong_nul_err : ∃ e, pyLoadLongLine [0x35, 0, nl] = .error e := ⟨_, rfl⟩

/-- `L5\0\n`: `PyLong_FromString` stops at the NUL (python/cpython#126996). -/
theorem longLineTwins_refuted : ¬ LongLineTwins := by
  intro h
  have := h [0x35, 0] (by decide)
  simp only [List.cons_append, List.nil_append] at this
  rw [cLoadLong_nul] at this
  obtain ⟨e, he⟩ := pyLoadLong_nul_err
  rw [he] at this
  simp [SameOutcome] at this

end PyLean.Pickle
