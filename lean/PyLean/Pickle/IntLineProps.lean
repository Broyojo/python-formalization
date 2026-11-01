import PyLean.Pickle.Long

/-!
The protocol-0 `INT` and `LONG` opcodes: the C and Python unpicklers parse
the text argument (`load_int`/`load_long`, `Lib/pickle.py:1376-1404` and
`Modules/_pickle.c:5398-5577`) differently.

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

theorem cLoadInt_sp1 : cLoadIntLine [0x20, 0x31, nl] = .ok (.bool true) := by decide +kernel
theorem pyLoadInt_sp1 : pyLoadIntLine [0x20, 0x31, nl] = .ok (.int 1) := by decide +kernel

/-- `I 1\n` is `True` in C (strtol reads 1 from a 3-byte line) and `1` in
Python, which only treats `00`/`01` as bools. python/cpython#135241 (fixed on
main). -/
theorem intLineTwins_refuted : ¬ IntLineTwins := by
  intro h
  have := h [0x20, 0x31] (by decide)
  simp only [List.cons_append, List.nil_append] at this
  rw [cLoadInt_sp1, pyLoadInt_sp1] at this
  simp [SameOutcome] at this

/-- The 3-byte lines that C's strtol reads as 0 or 1 but are not `00`/`01`:
an optional space or sign before the digit (`-1` is -1, not a bool). -/
def BoolSpelling (body : Bytes) : Prop :=
  ∃ a d, body = [a, d] ∧ (d = 0x30 ∨ d = 0x31) ∧ (isSpace a = true ∨ a = 0x2b ∨ (a = 0x2d ∧ d = 0x30))

/-- `IntLineTwins` without the bool spellings. -/
def IntLineTwinsNoBoolSpelling : Prop :=
  ∀ body : Bytes, nl ∉ body → ¬ BoolSpelling body →
    SameOutcome (cLoadIntLine (body ++ [nl])) (pyLoadIntLine (body ++ [nl]))

theorem cLoadInt_nul : cLoadIntLine [0x31, 0x32, 0, nl] = .ok (.int 12) := by decide +kernel
theorem pyLoadInt_nul_err : ∃ e, pyLoadIntLine [0x31, 0x32, 0, nl] = .error e := ⟨_, rfl⟩

/-- `I12\0\n`: C's strtol stops at the NUL that ends its C string and returns
12; `int(b'12\x00\n')` raises. python/cpython#126996 (open). -/
theorem intLineTwinsNoBoolSpelling_refuted : ¬ IntLineTwinsNoBoolSpelling := by
  intro h
  have := h [0x31, 0x32, 0] (by decide) (by
    rintro ⟨a, d, hb, _⟩; simp at hb)
  simp only [List.cons_append, List.nil_append] at this
  rw [cLoadInt_nul] at this
  obtain ⟨e, he⟩ := pyLoadInt_nul_err
  rw [he] at this
  simp [SameOutcome] at this

/-- `IntLineTwinsNoBoolSpelling` without NUL bytes in the line. -/
def IntLineTwinsNoNul : Prop :=
  ∀ body : Bytes, nl ∉ body → (0 : UInt8) ∉ body → ¬ BoolSpelling body →
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
theorem zeros5000one_not_bool : ¬ BoolSpelling zeros5000one := by
  rintro ⟨a, d, hb, _⟩
  have := congrArg List.length hb
  simp only [zeros5000one, List.length_append, List.length_replicate, List.length_cons,
    List.length_nil] at this
  omega

set_option maxRecDepth 200000 in
/-- `I` + 5000 zeros + `1`: C's strtol fast path returns 1 without the
4300-digit limit of `int()`, which the Python twin enforces. -/
theorem intLineTwinsNoNul_refuted : ¬ IntLineTwinsNoNul := by
  intro h
  have := h zeros5000one zeros5000one_no_nl zeros5000one_no_nul zeros5000one_not_bool
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
