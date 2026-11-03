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

def Outcome.isUB {σ : Type} : Outcome σ → Bool
  | .ub _ _ => true
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

/-- The raw stream's `readinto`, called by `read(1)` with the lock held (callback 4,
after the `readable()` and `tell()` of `__init__` and the `closed` of `CHECK_CLOSED`),
calls `__init__(raw, 8)` on the reader: `_buffered_init` frees the buffer and the lock
the read holds (bufferedio.c:846-860), and the read's `LEAVE_BUFFERED` then unlocks a
lock nobody holds, which aborts the process. The raw answers 1 without storing
anything, so nothing is written into the freed buffer first (that write would be
undefined behaviour of its own). -/
def reinitRaw : Raw := { plainRaw [120] with rs := [.bad 1], hooks := [(4, .reinit 8)] }

theorem bufferedCNoCrash_refuted_reinit : ¬BufferedCNoCrash := by
  intro h
  exact absurd (h 0 reinitRaw 8 [.read (some 1)]) (by decide +kernel)

/-- The same `__init__` from the `closed` property read by `CHECK_CLOSED`, before the
lock is taken, is harmless: the read goes on with the new buffer. -/
theorem reinit_unlocked_ok :
    (runC 0 { plainRaw [120] with hooks := [(3, .reinit 8)] } 8 [.read (some 1)]).results =
      [.ok (.bytes [120])] := by
  decide +kernel

/-- A re-entered `__init__(raw, 0)` fails, but only after storing `buffer_size = 0`
(bufferedio.c:1605, refused at :841). In `read(10)` on a reader of size 3 (not a
power of two, so `buffer_mask` is 0), the next `MINUS_LAST_BLOCK` divides by it:
the process dies of SIGFPE. That is x86-64, where the model's `crash` for a division by
zero holds (measured on 3.15.2); C calls it undefined behaviour, and on AArch64 `sdiv`
returns 0 instead of trapping. -/
def size0ReadRaw : Raw := { plainRaw (List.replicate 20 120) with hooks := [(4, .reinit 0)] }

theorem bufferedCNoCrash_refuted_size0 : ¬BufferedCNoCrash := by
  intro h
  exact absurd (h 0 size0ReadRaw 3 [.read (some 10)]) (by decide +kernel)

/-- No sequence of operations on `io.BufferedReader`, `BufferedWriter` or
`BufferedRandom` blocks the thread forever, whatever the raw stream answers and calls
back into. Invariant: no hang (and every loop of the C code ends). -/
def BufferedCNoHang : Prop := ∀ (kind : Nat) (raw : Raw) (size : Int) (ops : List BfOp),
  (runC kind raw size ops).isHung = false

/-- `write(10 bytes)` on a writer of size 5: its `raw.write` calls `__init__(raw, 0)`,
which leaves `buffer_size` 0; `while (remaining >= self->buffer_size)` (:2186) then
never ends, asking the raw stream to write `b''` again and again. -/
def size0WriteRaw : Raw := { plainRaw [] with hooks := [(4, .reinit 0)] }

theorem bufferedCNoHang_refuted : ¬BufferedCNoHang := by
  intro h
  exact absurd (h 1 size0WriteRaw 5 [.write [97, 98, 99, 100, 101, 102, 103, 104, 105, 106]]) (by decide +kernel)

/-- With a power-of-two size (here 8; the default 8192 too) `MINUS_LAST_BLOCK` uses
`buffer_mask` and does not trap: after a re-entered `__init__(raw, 0)`, `read(10)`
stops filling (`read_end < buffer_size` is false, :1858) and `PyBytesWriter_Finish`
(:1886) returns 10 bytes, the last 2 of which nobody wrote. -/
theorem size0_pow2_uninit :
    (runC 0 { plainRaw (List.replicate 20 120) with hooks := [(4, .reinit 0)] } 8 [.read (some 10)]).results =
      [.ok (.bytes (List.replicate 8 120 ++ [uninit, uninit]))] := by
  decide +kernel

/-- A refused `__init__(raw, -1)` stores `buffer_size = -1`: `MINUS_LAST_BLOCK` then
computes `-1 * (1 / -1) = 1` (C division truncates) and `read(10)` returns 10 bytes. -/
theorem reinit_negative_read :
    (runC 0 { plainRaw (List.replicate 20 120) with hooks := [(4, .reinit (-1))] } 3 [.read (some 10)]).results =
      [.ok (.bytes (List.replicate 10 120))] := by
  decide +kernel

/-- In `write(10 bytes)` on a writer of size 5 whose `raw.write` re-enters
`__init__(raw, s)` and answers `None`: with `s = -1`, `memcpy(self->buffer, ...,
self->buffer_size)` (:2195-2196) is given a huge `size_t`: undefined behaviour, which
is why the model claims no outcome. What happens depends on the heap layout: we measured
SIGSEGV for this writer, a reviewer's raw got `BlockingIOError` with
`characters_written` -1, and a `BufferedRandom` ran on with a corrupted heap;
with `s = 0` it copies nothing and the write raises `BlockingIOError` (0 written). -/
theorem reinit_negative_write :
    (runC 1 { plainRaw [] with ws := [.block], hooks := [(4, .reinit (-1))] } 5
      [.write [97, 98, 99, 100, 101, 102, 103, 104, 105, 106]]).isUB = true ∧
    (runC 1 { plainRaw [] with ws := [.block], hooks := [(4, .reinit 0)] } 5
      [.write [97, 98, 99, 100, 101, 102, 103, 104, 105, 106]]).results =
      [.error (BC2.blocking 0)] := by
  decide +kernel

/-- A re-entered `__init__(raw, 2**48)` frees the buffer (:846-847) and fails to
allocate the new one (:848-851): `self->buffer` is `NULL` when `read(4)` on a reader of
size 8 copies the filled bytes out of it with `memcpy(out, self->buffer + self->pos, 4)`
(:1877) at `pos` 0, an address below `unmappedBelow` (a platform assumption: Linux with
`vm.mmap_min_addr` at least 4096), and the process dies (measured: SIGSEGV). The raw answers 8 without storing anything, so nothing is
written into the freed buffer before that. -/
theorem reinit_nomem_read_crash :
    (runC 0 { plainRaw (List.replicate 20 120) with rs := [.bad 8], hooks := [(4, .reinit (2 ^ 48))] } 8
      [.read (some 4)]).isCrashed = true := by
  decide +kernel

/-- The same `NULL` buffer read by `peek()` after its fill: the copy is
`PyBytes_FromStringAndSize(self->buffer, r)` (:1917), and a `NULL` pointer asks for `r`
uninitialized bytes (Objects/bytesobject.c:132-145), so nothing faults and the caller
gets a byte nobody wrote. -/
theorem reinit_nomem_peek_uninit :
    (runC 0 { plainRaw [] with rs := [.bad 1], hooks := [(4, .reinit (2 ^ 48))] } 16
      [.peek 0]).results = [.ok (.bytes [uninit])] := by
  decide +kernel

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
