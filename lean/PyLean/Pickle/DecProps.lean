import PyLean.Pickle.Diff
import PyLean.Pickle.IntLineProps

/-!
`pickle.loads` (C) vs `pickle._loads` (Python) on whole byte streams.
-/

namespace PyLean.Pickle

open PyLean

/-- The decoded object with the heap resolved, so that heap addresses do not
matter. -/
def resolved (r : Py (DV × Heap)) : Py Lean.Json := (fun p => dvJson p.2 100000 [] p.1) <$> r

/-- The class name of a raised exception, `""` for a result. -/
def clsOf {α : Type} : Py α → String
  | .ok _ => ""
  | .error e => e.className

/-- Neither unpickler reaches an opcode the model excludes (floats, persistent
ids, out-of-band buffers, anything that runs code; the five globals the
picklers emit for plain data are allowed). -/
abbrev DataOnly (data : Bytes) : Prop :=
  clsOf (cLoads data) ≠ "Excluded" ∧ clsOf (pyLoads data) ≠ "Excluded"

theorem not_same_ok_err {r1 r2 : Py (DV × Heap)} (h1 : isErr r1 = false) (h2 : isErr r2 = true) :
    ¬ SameOutcome (resolved r1) (resolved r2) := by
  cases r1 with
  | error e => simp [isErr] at h1
  | ok a =>
    cases r2 with
    | ok b => simp [isErr] at h2
    | error e => simp [resolved, SameOutcome, Functor.map, Except.map]

theorem not_same_err_ok {r1 r2 : Py (DV × Heap)} (h1 : isErr r1 = true) (h2 : isErr r2 = false) :
    ¬ SameOutcome (resolved r1) (resolved r2) := by
  cases r2 with
  | error e => simp [isErr] at h2
  | ok a =>
    cases r1 with
    | ok b => simp [isErr] at h1
    | error e => simp [resolved, SameOutcome, Functor.map, Except.map]

/-- On every stream the two unpicklers return the same object or raise the same
exception class and message. Source: twin agreement. -/
def LoadsTwinsExact : Prop :=
  ∀ data : Bytes, DataOnly data → clsOf (cLoads data) = clsOf (pyLoads data)

/-- `POP` on an empty stack: `UnpicklingError` in C, a raw `IndexError` from
`list.pop` in Python. -/
theorem loadsTwinsExact_refuted : ¬ LoadsTwinsExact := by
  intro h
  have := h [oPOP] (by decide +kernel)
  revert this
  decide +kernel

/-- The two unpicklers accept the same streams (of data opcodes) and return
equal objects. Source: twin agreement. `IntLineTwins` and `LongLineTwins`
record the divergences in the text opcodes. -/
def LoadsTwinsAccept : Prop :=
  ∀ data : Bytes, DataOnly data → SameOutcome (resolved (cLoads data)) (resolved (pyLoads data))

def emptyAppends : Bytes := [oNONE, oMARK, oAPPENDS, oSTOP]

/-- `APPENDS` with no items on `None`: C returns early (`len == x`), Python
looks up `.append` and raises `AttributeError`. python/cpython#135573, fixed on
main. -/
theorem loadsTwinsAccept_refuted : ¬ LoadsTwinsAccept := by
  intro h
  exact not_same_ok_err (by decide +kernel) (by decide +kernel) (h emptyAppends (by decide +kernel))

/-- A frame claiming `n` bytes around `body`: both unpicklers accept the same
streams. PEP 3154: a frame of the stated length. -/
def FrameTwins : Prop :=
  ∀ (n : Nat) (body : Bytes), n < 2 ^ 63 →
    let data := oFRAME :: leBytes n 8 ++ body
    DataOnly data → SameOutcome (resolved (cLoads data)) (resolved (pyLoads data))

/-- A `FRAME` that claims 3 bytes with only 2 left: C reports truncation,
Python builds a short frame and returns the object. python/cpython#128853;
main's Python raises `EOFError`. -/
theorem frameTwins_refuted : ¬ FrameTwins := by
  intro h
  have := h 3 [oNONE, oSTOP] (by decide) (by decide +kernel)
  exact not_same_err_ok (by decide +kernel) (by decide +kernel) this

/-- `PUT` with a decimal index: both unpicklers accept the same indices. -/
def PutTwins : Prop :=
  ∀ i : Nat,
    let data := oNONE :: oPUT :: decDigits i ++ [nl, oSTOP]
    DataOnly data → SameOutcome (resolved (cLoads data)) (resolved (pyLoads data))

/-- `PUT` with index `2**63`: `PyLong_AsSsize_t` raises `OverflowError` in C,
the Python memo is a dict. python/cpython#144410, closed as not a bug. -/
theorem putTwins_refuted : ¬ PutTwins := by
  intro h
  have := h 9223372036854775808 (by decide +kernel)
  exact not_same_err_ok (by decide +kernel) (by decide +kernel) this

end PyLean.Pickle
