import PyLean.PyIO.BufLock

/-!
The buffered constructors (`_io_BufferedReader___init___impl`,
`_io_BufferedWriter___init___impl`, `_io_BufferedRandom___init___impl` with
`_buffered_init`, Modules/_io/bufferedio.c; `BufferedReader.__init__`,
`BufferedWriter.__init__`, `BufferedRandom.__init__`, Lib/_pyio.py) over a raw stream
whose inquiries answer a `bool`: which check refuses the construction, in which
order and with which exception, and what an accepted construction builds. The twin
refutations in `BufReentry.lean` are about inquiries that answer other objects.
-/

namespace PyLean.PyIO

open PyLean

/-- A raw stream whose `seekable()`, `readable()` and `writable()` answer its own
flags as `bool`s (each may be `False`), whose `tell()` answers its position (or raises
`OSError` when it is not seekable), that is open, and that calls nothing back. -/
structure HonestRaw (raw : Raw) : Prop where
  qs : raw.qs = []
  hooks : raw.hooks = []
  ss : raw.ss = []
  closed : raw.closed = false

/-- The raw calls of an accepted C construction, in order: the inquiries
(bufferedio.c:1600, :1952, :2493-2501), then `_buffered_raw_tell` (:869-870). -/
def cInitCalls : Nat → List RCall
  | 0 => [.readable, .tell]
  | 1 => [.writable, .tell]
  | _ => [.seekable, .readable, .writable, .tell]

/-- The raw calls of an accepted `_pyio` construction: `raw.readable()`
(_pyio.py:1052), `raw.writable()` (:1248), `raw._checkSeekable()` (:1426, :430-435)
first for a `BufferedRandom`, and no `tell`. -/
def pyInitCalls : Nat → List RCall
  | 0 => [.readable]
  | 1 => [.writable]
  | _ => [.seekable, .readable, .writable]

/-- The raw after `calls`: each one logged and counted, nothing else changed. -/
def afterCalls (raw : Raw) (calls : List RCall) : Raw :=
  calls.foldl (fun r c => { r with tick := r.tick + 1, log := r.log ++ [c] }) raw

/-- What refuses `io.Buffered*(raw, size)`, first match first, with the raw calls made
before it: the `buffer_size: Py_ssize_t` converter (clinic/bufferedio.c.h,
`PyLong_AsSsize_t`) before the body, so before any call on the raw; the inquiries of
the type, each refusing `False` with `UnsupportedOperation` (`_PyIOBase_check_*`,
Modules/_io/iobase.c:413-428, :446-461, :479-494), all of them before the size; then
`_buffered_init`: `size <= 0` (:841-845) and a buffer the allocator refuses
(:848-851). `none`: accepted. -/
def cInitRefusal (alloc kind : Nat) (raw : Raw) (size : Int) : Option (PyExc × List RCall) :=
  if ¬ InSsize size then some (.overflowError "Python int too large to convert to C ssize_t", [])
  else if kind = 2 ∧ raw.canSeek = false then some (unsupportedOp "File or stream is not seekable.", [.seekable])
  else if kind ≠ 1 ∧ raw.canRead = false then
    some (unsupportedOp "File or stream is not readable.", if kind = 2 then [.seekable, .readable] else [.readable])
  else if kind ≠ 0 ∧ raw.canWrite = false then
    some (unsupportedOp "File or stream is not writable.", (cInitCalls kind).dropLast)
  else if size ≤ 0 then some (.valueError "buffer size must be strictly positive", (cInitCalls kind).dropLast)
  else if size ≥ alloc then some (memoryError, (cInitCalls kind).dropLast)
  else none

/-- `io.BufferedReader(raw, size)` (`kind` 0), `BufferedWriter` (1) and
`BufferedRandom` (2), C twin, on a machine whose allocator grants exactly the
requests below `alloc` (an oracle: every outcome of the one `PyMem_Malloc` is some
`alloc`), over every honest raw and every size:

1. a construction `cInitRefusal` refuses raises exactly that exception, after exactly
   those raw calls (none for a size outside `Py_ssize_t`; a false inquiry wins over a
   bad size, and a size refusal comes only once every inquiry answered `True`), with
   the raw's contents and position untouched;
2. an accepted one succeeds and sets what the body sets: `ok`, the raw attached and
   not detached, `buffer_size` = `size`, a buffer of `size` bytes, a free lock,
   `buffer_mask` = `size - 1` for a power of two and 0 otherwise (:863-868),
   `abs_pos` from the raw's `tell()` when it is seekable and the answer fits
   `Py_off_t`, else the zeroed 0 (a failed `_buffered_raw_tell` is cleared,
   :869-870), an empty read buffer for a reader (`_bufferedreader_reset_buf`,
   `read_end` -1) and an empty write buffer at 0 for a writer
   (`_bufferedwriter_reset_buf`, `pos` 0); the raw has seen exactly
   `cInitCalls kind`, and its contents and position are untouched.

The new lock is assumed allocated (the `RuntimeError` of :856-859 is not modelled).
`kind ≤ 2` names the three types. -/
def CInitSpec : Prop := ∀ (alloc kind : Nat) (raw : Raw) (size : Int), kind ≤ 2 → HonestRaw raw →
  (∀ e calls, cInitRefusal alloc kind raw size = some (e, calls) → ∃ s,
    runCAlloc alloc kind raw size [] = .initErr s e ∧
    s.raw.log = raw.log ++ calls ∧ s.raw.data = raw.data ∧ s.raw.pos = raw.pos) ∧
  (cInitRefusal alloc kind raw size = none → ∃ s, runCAlloc alloc kind raw size [] = .done s [] ∧
    s.ok = true ∧ s.detached = false ∧ s.rawNull = false ∧ s.locked = false ∧
    s.size = size ∧ s.hasBuf = true ∧ s.buffer.length = size.toNat ∧
    s.mask = (if size.toNat &&& (size.toNat - 1) = 0 then size.toNat - 1 else 0) ∧
    s.absPos = (if raw.canSeek = true ∧ InSsize raw.pos then (raw.pos : Int) else 0) ∧
    (kind ≠ 1 → s.readEnd = -1) ∧ (kind ≠ 0 → s.writePos = 0 ∧ s.writeEnd = -1 ∧ s.pos = 0) ∧
    s.raw.log = raw.log ++ cInitCalls kind ∧ s.raw.data = raw.data ∧ s.raw.pos = raw.pos)

/-- What refuses `_pyio.Buffered*(raw, size)`, first match first, with the raw calls
made before it. A `BufferedRandom` asks `seekable()` (`UnsupportedOperation`,
_pyio.py:430-435), then runs `BufferedReader.__init__` (`raw.readable()` falsy:
`OSError`, :1052-1053; then the size, :1056-1057) before `BufferedWriter.__init__`
(`raw.writable()` falsy: `OSError`, :1248-1249; then the size, :1252-1253). The size is
any Python int (no C conversion), and nothing is allocated. -/
def pyInitRefusal (kind : Nat) (raw : Raw) (size : Int) : Option (PyExc × List RCall) :=
  let reader : List RCall := if kind = 2 then [.seekable, .readable] else [.readable]
  if kind = 2 ∧ raw.canSeek = false then some (unsupportedOp "File or stream is not seekable.", [.seekable])
  else if kind ≠ 1 ∧ raw.canRead = false then some (osError "\"raw\" argument must be readable.", reader)
  else if kind ≠ 1 ∧ size ≤ 0 then some (.valueError "invalid buffer size", reader)
  else if kind ≠ 0 ∧ raw.canWrite = false then
    some (osError "\"raw\" argument must be writable.", pyInitCalls kind)
  else if size ≤ 0 then some (.valueError "invalid buffer size", pyInitCalls kind)
  else none

/-- `_pyio.BufferedReader(raw, size)`, `BufferedWriter`, `BufferedRandom` over every
honest raw and every size: a construction `pyInitRefusal` refuses raises exactly that
exception after exactly those raw calls (a falsy inquiry gives its own `OSError` or
`UnsupportedOperation`); an
accepted one succeeds, the object attached, its `buffer_size` = `size`, a reader's read
buffer empty at 0 with a free `_read_lock` (:1058-1060, `_reset_read_buf`
:1065-1067), a writer's write buffer empty with a free `_write_lock` (:1254-1256); the
raw has seen exactly `pyInitCalls kind` (its call counter restarts at 0: the harness
arms its hooks once the constructor has returned). -/
def PyInitSpec : Prop := ∀ (kind : Nat) (raw : Raw) (size : Int), kind ≤ 2 → HonestRaw raw →
  (∀ e calls, pyInitRefusal kind raw size = some (e, calls) → ∃ s,
    runP kind raw size [] = .initErr s e ∧ s.raw.log = raw.log ++ calls) ∧
  (pyInitRefusal kind raw size = none → ∃ s, runP kind raw size [] = .done s [] ∧
    s.detached = false ∧ s.kind = kind ∧ s.size = size.toNat ∧ s.hung = false ∧
    (kind ≠ 1 → s.readBuf = [] ∧ s.readPos = 0 ∧ s.rl = false) ∧
    (kind ≠ 0 → s.writeBuf = [] ∧ s.wl = false) ∧
    s.raw = { afterCalls raw (pyInitCalls kind) with tick := 0 })

/-- Close the conjuncts about a computed state. -/
macro "init_fields" : tactic => `(tactic|
  all_goals first
    | rfl
    | (intro h; exact absurd rfl h)
    | (intro _; rfl)
    | (intro _; exact ⟨rfl, rfl, rfl⟩)
    | (intro _; exact ⟨rfl, rfl⟩)
    | simp [afterCalls, cInitCalls, pyInitCalls, *]
    | (simp [afterCalls, cInitCalls, pyInitCalls]; done))

theorem cInitSpec_proven : CInitSpec := by
  intro alloc kind raw size hk h
  obtain ⟨data, pos, rs, ws, ss, excMro, cs, qs, fr, cr, cw, csk, closed, cf, hooks, tick, log⟩ := raw
  obtain ⟨hq, hh, hs, hc⟩ := h
  dsimp only at hq hh hs hc
  subst hq hh hs hc
  have hn : ¬ ((pos : Int) < 0) := by omega
  obtain rfl | rfl | rfl : kind = 0 ∨ kind = 1 ∨ kind = 2 := by omega
  all_goals cases cr <;> cases cw <;> cases csk
  all_goals by_cases hz : InSsize size
  all_goals by_cases h0 : size ≤ 0
  all_goals by_cases ha : size ≥ (alloc : Int)
  all_goals refine ⟨fun e calls he => ?_, fun he => ?_⟩
  all_goals simp (config := { decide := true }) only [cInitRefusal, cInitCalls, List.dropLast, hz, h0, ha,
    ↓reduceIte, reduceCtorEq, Option.some.injEq, Prod.mk.injEq, not_true, not_false_eq_true] at he
  all_goals first
    | (obtain ⟨rfl, rfl⟩ := he
       simp (config := { decide := true }) only [runCAlloc, argSsize, BC2.init, BC2.bind_def, BC2.mod,
         BC2.get, BC2.put, BC2.thr, BC2.pure_apply, BC2.inquiryObj, BC2.onRawObj, BC2.callback, BC2.ofPy,
         BC2.checkInq, BC2.attempt, Raw.enter, Raw.inquire, List.find?, Option.map, hz, h0, ha,
         ↓reduceIte, reduceCtorEq]
       refine ⟨_, rfl, ?_⟩
       refine ⟨?_, ?_, ?_⟩
       init_fields
       done)
    | (by_cases hp : InSsize (pos : Int)
       all_goals
         simp (config := { decide := true }) only [runCAlloc, argSsize, hz, BC2.init, BC2.bind_def, BC2.mod, BC2.get,
           BC2.put, BC2.thr, BC2.pure_apply, BC2.inquiryObj, BC2.onRawObj, BC2.callback, BC2.ofPy,
           BC2.checkInq, BC2.attempt, BC2.rawTell, BC2.onRaw, BC2.checkPos, BC2.asOff, Raw.enter,
           Raw.inquire, Raw.tell, Raw.popS, List.find?, Option.map, h0, ha, hp, hn, ↓reduceIte,
           reduceCtorEq]
         refine ⟨_, rfl, ?_⟩
         refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
         init_fields
       done)

theorem pyInitSpec_proven : PyInitSpec := by
  intro kind raw size hk h
  obtain ⟨data, pos, rs, ws, ss, excMro, cs, qs, fr, cr, cw, csk, closed, cf, hooks, tick, log⟩ := raw
  obtain ⟨hq, hh, hs, hc⟩ := h
  dsimp only at hq hh hs hc
  subst hq hh hs hc
  obtain rfl | rfl | rfl : kind = 0 ∨ kind = 1 ∨ kind = 2 := by omega
  all_goals cases cr <;> cases cw <;> cases csk
  all_goals by_cases h0 : size ≤ 0
  all_goals refine ⟨fun e calls he => ?_, fun he => ?_⟩
  all_goals simp (config := { decide := true }) only [pyInitRefusal, pyInitCalls, h0, ↓reduceIte,
    reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at he
  all_goals first
    | (obtain ⟨rfl, rfl⟩ := he
       unfold runP BP2.init
       simp only [h0, ↓reduceIte]
       refine ⟨_, rfl, ?_⟩
       init_fields
       done)
    | (unfold runP BP2.init
       simp only [h0, ↓reduceIte]
       refine ⟨_, rfl, ?_⟩
       refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
       init_fields
       done)

end PyLean.PyIO
