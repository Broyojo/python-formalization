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

/-- On every stream the two unpicklers raise the same exception class, or
neither raises. Source: twin agreement. -/
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

/-- `I12\0\n.`: the line C's strtol accepts and `int()` rejects, as a whole
stream. -/
def nulIntStream : Bytes := [oINT, 0x31, 0x32, 0, nl, oSTOP]

/-- python/cpython#126996 (open). The empty `APPENDS` of python/cpython#135573 no
longer differs: `do_append` looks up `.append` as Python does. -/
theorem loadsTwinsAccept_refuted : ¬ LoadsTwinsAccept := by
  intro h
  exact not_same_ok_err (by decide +kernel) (by decide +kernel) (h nulIntStream (by decide +kernel))

/-- A frame claiming `n` bytes around `body`: both unpicklers accept the same
streams. PEP 3154: a frame of the stated length. -/
def FrameTwins : Prop :=
  ∀ (n : Nat) (body : Bytes), n < 2 ^ 63 →
    let data := oFRAME :: leBytes n 8 ++ body
    DataOnly data → SameOutcome (resolved (cLoads data)) (resolved (pyLoads data))

theorem nulFrame_c : isErr (cLoads (oFRAME :: leBytes 6 8 ++ nulIntStream)) = false := by decide +kernel
theorem nulFrame_py : isErr (pyLoads (oFRAME :: leBytes 6 8 ++ nulIntStream)) = true := by decide +kernel
theorem nulFrame_dataOnly : DataOnly (oFRAME :: leBytes 6 8 ++ nulIntStream) := by decide +kernel

seal SameOutcome in
/-- A frame holding the stream of `loadsTwinsAccept_refuted`: the bodies are
unconstrained, so what differs outside a frame differs inside one. A frame longer
than the data no longer differs: `FrameRead`. -/
theorem frameTwins_refuted : ¬ FrameTwins := fun h =>
  not_same_ok_err nulFrame_c nulFrame_py (h 6 nulIntStream (by decide) nulFrame_dataOnly)

/-- `BINPUT k` of `None`, then `MEMOIZE` of 7, then `BINGET i`. -/
def memoStream (k i : UInt8) : Bytes :=
  [oNONE, oBINPUT, k, oBININT1, 7, oMEMOIZE, oPOP, oBINGET, i, oSTOP]

/-- `MEMOIZE` stores under the same index in both unpicklers, whatever `BINPUT` came
first. Source: `Lib/pickletools.py:1874-1875`, "The index of the memo location to
write is the number of elements currently present in the memo." -/
def MemoizeTwins : Prop :=
  ∀ k i : UInt8, SameOutcome (resolved (cLoads (memoStream k i))) (resolved (pyLoads (memoStream k i)))

theorem memoStream_c : isErr (cLoads (memoStream 200 1)) = true := by decide +kernel
theorem memoStream_py : isErr (pyLoads (memoStream 200 1)) = false := by decide +kernel

seal SameOutcome in
/-- `_Unpickler_MemoPut` stores a sparse key in `memo_dict` without counting it,
and `load_memoize` writes at `memo_len`, so the two memos part after one sparse
`BINPUT`. Through 3.14 `memo_len` counted every key. -/
theorem memoizeTwins_refuted : ¬ MemoizeTwins := fun h =>
  not_same_err_ok memoStream_c memoStream_py (h 200 1)

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
