import PyLean.PyIO.BufProps

/-!
Properties of the buffered classes over a raw stream that is a fallible,
re-entrant Python object (`PyIO/BufRaw.lean`): crashes, uninitialized memory,
deadlocks, a failed seek, and the checks the C code makes on what the raw answers.
-/

namespace PyLean.PyIO

open PyLean

def Outcome.isCrashed {σ : Type} : Outcome σ → Bool
  | .crashed => true
  | _ => false

def Outcome.isHung {σ : Type} : Outcome σ → Bool
  | .hung => true
  | _ => false

def Outcome.isInitErr {σ : Type} : Outcome σ → Bool
  | .initErr _ => true
  | _ => false

def Outcome.results {σ : Type} : Outcome σ → List (Py Val)
  | .done _ rs => rs
  | _ => []

/-- Every byte inside a result. -/
def Atom.allBytes : Atom → List Nat
  | .bytes b => b
  | _ => []

def resultBytes : Py Val → List Nat
  | .ok (.atom a) => a.allBytes
  | .ok (.list l) => l.flatMap Atom.allBytes
  | .error _ => []

/-! ## No crash -/

/-- No sequence of operations on `io.BufferedReader`, `BufferedWriter` or
`BufferedRandom` over a raw stream written in Python kills the interpreter,
whatever the raw answers and whatever it calls back into. Invariant: pure Python
code cannot crash the interpreter. -/
def BufferedCNoCrash : Prop := ∀ (kind : Nat) (raw : Raw) (size : Int) (ops : List BfOp),
  (runC kind raw size ops).isCrashed = false

/-- The raw stream's `closed` property, read by `CHECK_CLOSED` in `read(1)` before the
lock is taken (callback 3, after the `readable()` and `tell()` of `__init__`), detaches
the reader: `self->raw` is NULL when the read fills the buffer. -/
def detachingRaw : Raw := { plainRaw [120] with hooks := [(3, .detach)] }

theorem bufferedCNoCrash_refuted : ¬BufferedCNoCrash := by
  intro h
  exact absurd (h 0 detachingRaw 8 [.read (some 1)]) (by decide +kernel)

/-! ## Uninitialized memory -/

/-- Every byte that `io.BufferedReader` hands back was stored by somebody: it is
never memory that nobody wrote (`uninit`). Invariant: no uninitialized memory
reaches Python objects. -/
def BufferedReaderNoUninit : Prop := ∀ (raw : Raw) (size : Int) (ops : List BfOp),
  ∀ r ∈ (runC 0 raw size ops).results, ∀ b ∈ resultBytes r, b < uninit

/-- `readinto` answers `len(b)` without storing anything, as the reproducer's `Liar`
does: `peek()` on a fresh reader fills the `PyMem_Malloc`ed buffer (bufferedio.c:848)
through `_bufferedreader_fill_buffer` and returns its 16 bytes, which nobody wrote. -/
def lyingRaw : Raw := { plainRaw [] with rs := [.bad 16] }

theorem bufferedReaderNoUninit_refuted : ¬BufferedReaderNoUninit := by
  intro h
  exact absurd (h lyingRaw 16 [.peek 0] (.ok (.bytes (List.replicate 16 uninit))) (by decide +kernel)
    uninit (by decide)) (by decide)

/-- `read1(1)` reads straight into a fresh `PyBytesWriter` (bufferedio.c:1074-1091). -/
theorem lyingRaw_read1 :
    (runC 0 { plainRaw [] with rs := [.bad 1] } 4 [.read1 1]).results = [.ok (.bytes [uninit])] := by
  decide +kernel

/-- `read1(n)` never returns memory nobody wrote, for every raw stream, buffer size
and `n`. Invariant, for the direct read into a `PyBytesWriter`
(bufferedio.c:1074-1091). -/
def BufferedRead1NoUninit : Prop := ∀ (raw : Raw) (size n : Int),
  ∀ r ∈ (runC 0 raw size [.read1 n]).results, ∀ b ∈ resultBytes r, b < uninit

/-- `read1(1)` on a fresh reader whose `readinto` answers 1 and stores nothing:
`PyBytesWriter_FinishWithSize(writer, 1)` keeps a byte nobody wrote. -/
theorem bufferedRead1NoUninit_refuted : ¬BufferedRead1NoUninit := by
  intro h
  exact absurd (h { plainRaw [] with rs := [.bad 1] } 4 1 (.ok (.bytes [uninit])) (by decide +kernel)
    uninit (by decide)) (by decide)

/-- The deterministic half of the reproducer: after an honest fill of `abcd`, a fill
that only claims 4 bytes hands back the stale `a` in C, and a zero byte in `_pyio`
(`RawIOBase.read` zeroes its bytearray, _pyio.py:620). -/
theorem lyingRaw_stale :
    (runC 0 { plainRaw [97, 98, 99, 100] with rs := [.short 4, .bad 4] } 4
      [.read (some 1), .read (some 3), .read (some 1)]).results =
      [.ok (.bytes [97]), .ok (.bytes [98, 99, 100]), .ok (.bytes [97])] ∧
    (runP 0 { plainRaw [97, 98, 99, 100] with rs := [.short 4, .bad 4] } 4
      [.read (some 1), .read (some 3), .read (some 1)]).results =
      [.ok (.bytes [97]), .ok (.bytes [98, 99, 100]), .ok (.bytes [0])] := by
  decide +kernel

/-! ## No hang -/

/-- No sequence of operations on `_pyio.BufferedReader`, `BufferedWriter` or
`BufferedRandom` blocks the thread forever. Invariant (and what the C twin
guarantees with its "reentrant call" check, bufferedio.c:299-303). -/
def PyBufferedNoHang : Prop := ∀ (kind : Nat) (raw : Raw) (size : Int) (ops : List BfOp),
  (runP kind raw size ops).isHung = false

/-- `readinto` of the raw calls `read(1)` on the reader that is reading from it. -/
def reenteringRaw : Raw := { plainRaw [120] with hooks := [(1, .read (some 1))] }

theorem pyBufferedNoHang_refuted : ¬PyBufferedNoHang := by
  intro h
  exact absurd (h 0 reenteringRaw 8 [.read (some 1)]) (by decide +kernel)

/-- The C twin, with the hook on its `readinto` (its callbacks before that are the
`readable()` and `tell()` of `__init__` and the `closed` of `CHECK_CLOSED`): the re-entered `read(1)`
raises `RuntimeError("reentrant call inside <_io.BufferedReader>")` at
`ENTER_BUFFERED`, and the outer read completes. -/
def reenteringRawC : Raw := { plainRaw [120] with hooks := [(4, .read (some 1))] }

theorem reenteringRaw_c :
    (runC 0 reenteringRawC 8 [.read (some 1)]).results = [.ok (.bytes [120])] ∧
    (match runC 0 reenteringRawC 8 [.read (some 1)] with
     | .done s _ => s.raw.log.contains
         (.re (.error (.named "RuntimeError" "reentrant call inside <_io.BufferedReader>")))
     | _ => false) = true := by
  decide +kernel

/-! ## What the constructors accept -/

/-- `io.BufferedReader(raw)` and `_pyio.BufferedReader(raw)` accept the same raw
streams, for every raw (whatever its `readable()` answers) and buffer size.
Twin agreement. -/
def ReaderInitTwins : Prop := ∀ (raw : Raw) (size : Int),
  (runC 0 raw size []).isInitErr = (runP 0 raw size []).isInitErr

/-- `io.BufferedWriter(raw)` and `_pyio.BufferedWriter(raw)` accept the same raw streams. -/
def WriterInitTwins : Prop := ∀ (raw : Raw) (size : Int),
  (runC 1 raw size []).isInitErr = (runP 1 raw size []).isInitErr

/-- `io.BufferedRandom(raw)` and `_pyio.BufferedRandom(raw)` accept the same raw streams. -/
def RandomInitTwins : Prop := ∀ (raw : Raw) (size : Int),
  (runC 2 raw size []).isInitErr = (runP 2 raw size []).isInitErr

/-- An inquiry that answers `1`: `_PyIOBase_check_*` requires `True` itself
(Modules/_io/iobase.c:413-428, :446-461, :479-494), `_pyio` only a truthy value
(_pyio.py:1052, :1248, :430-435). -/
def oneRaw : Raw := { plainRaw [] with qs := [.int 1] }

theorem readerInitTwins_refuted : ¬ReaderInitTwins := by
  intro h; exact absurd (h oneRaw 8) (by decide +kernel)

theorem writerInitTwins_refuted : ¬WriterInitTwins := by
  intro h; exact absurd (h oneRaw 8) (by decide +kernel)

/-- `seekable()` is asked first by both random constructors. -/
theorem randomInitTwins_refuted : ¬RandomInitTwins := by
  intro h; exact absurd (h oneRaw 8) (by decide +kernel)

/-! ## A seek that fails -/

/-- `read(k)`, then `seek(p)` (which the raw refuses for `p < 0`, as `lseek` does
with `EINVAL`), then `tell()`, on a `BufferedRandom` over a raw holding `d`. -/
def randomTellAfterFailedSeek (c : Bool) (d : List Nat) (size : Int) (k : Nat) (p : Int) : Py Val :=
  let ops := [BfOp.read (some k), .seek p 0, .tell]
  if c then lastResult (runC 2 (plainRaw d) size ops) else lastResult (runP 2 (plainRaw d) size ops)

/-- For every contents, buffer size, read length and target, the twins report the
same position after a `seek` that the raw stream refused. The only hypothesis is
the constructor's `size > 0`. Twin agreement; and an invariant: an operation that
raises leaves the position where it was. -/
def RandomFailedSeekTwins : Prop := ∀ (d : List Nat) (size : Int) (k : Nat) (p : Int), size > 0 →
  randomTellAfterFailedSeek true d size k p = randomTellAfterFailedSeek false d size k p

theorem randomFailedSeekTwins_refuted : ¬RandomFailedSeekTwins := by
  intro h
  exact absurd (h [48, 49, 50, 51, 52, 53, 54, 55, 56, 57] 8 2 (-1) (by decide)) (by decide +kernel)

end PyLean.PyIO
