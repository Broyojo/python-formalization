import PyLean.PyIO.BufOps

/-! Properties of `BufferedReader`/`Writer`/`Random` (`Modules/_io/bufferedio.c`
and `Lib/_pyio.py`), over the raw stream of `PyIO/BufRaw.lean`. -/

namespace PyLean.PyIO

open PyLean

/-- A seekable raw stream over `d` that follows its contract: no scripted short
reads, blocking, bad counts or exceptions. -/
def plainRaw (d : List Nat) : Raw :=
  ⟨d, 0, [], [], [], true, true, true, false, none, []⟩

/-- `read(k)` then `readinto(bytearray(n))` on a new `BufferedReader(raw, size)`,
C twin. -/
def cReadThenInto (d : List Nat) (size : Int) (k n : Nat) : Py Val :=
  match BC2.init 0 (plainRaw d) size with
  | .error e => .error e
  | .ok s => (BC2.stepOp (BC2.stepOp s (.read (some k))).1 (.readinto n)).2

/-- The same two calls on `_pyio.BufferedReader`. -/
def pyReadThenInto (d : List Nat) (size : Int) (k n : Nat) : Py Val :=
  match BP2.init 0 (plainRaw d) size with
  | .error e => .error e
  | .ok s => (BP2.stepOp (BP2.stepOp s (.read (some k))).1 (.readinto n)).2

/-- For every contents, every positive buffer size and all `k`, `n`, after
`read(k)` the twins agree on whether `readinto` of an `n`-byte buffer succeeds.
The only hypothesis is the constructor's precondition `size > 0`. -/
def BufferedReaderReadintoTwins : Prop := ∀ (d : List Nat) (size : Int) (k n : Nat), size > 0 →
  (cReadThenInto d size k n).toBool = (pyReadThenInto d size k n).toBool

theorem bufferedReaderReadintoTwins_refuted : ¬BufferedReaderReadintoTwins := by
  intro h
  exact absurd (h [97, 98, 99, 100, 101, 102, 103, 104, 105, 106] 3 1 3 (by decide)) (by decide +kernel)

end PyLean.PyIO
