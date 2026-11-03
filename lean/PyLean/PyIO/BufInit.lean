import PyLean.PyIO.BufLock

/-!
The success path of the buffered constructors (`_io_BufferedReader___init___impl`,
`_io_BufferedWriter___init___impl`, `_io_BufferedRandom___init___impl` with
`_buffered_init`, Modules/_io/bufferedio.c; `BufferedReader.__init__`,
`BufferedWriter.__init__`, `BufferedRandom.__init__`, Lib/_pyio.py), and the size
checks that refuse it. The twin refutations in `BufReentry.lean` are about which raw
streams each accepts; these say what an accepted construction builds.
-/

namespace PyLean.PyIO

open PyLean

/-- A raw stream whose `seekable()`, `readable()` and `writable()` all answer `True`,
whose `tell()` answers its position, that is open, and that calls nothing back. -/
structure HonestRaw (raw : Raw) : Prop where
  qs : raw.qs = []
  hooks : raw.hooks = []
  ss : raw.ss = []
  canRead : raw.canRead = true
  canWrite : raw.canWrite = true
  canSeek : raw.canSeek = true
  closed : raw.closed = false

/-- The raw calls of a C constructor, in order: the inquiries
(bufferedio.c:1600, :1952, :2493-2501), then `_buffered_raw_tell` (:869-870). -/
def cInitCalls : Nat → List RCall
  | 0 => [.readable, .tell]
  | 1 => [.writable, .tell]
  | _ => [.seekable, .readable, .writable, .tell]

/-- The raw calls of a `_pyio` constructor: `raw.readable()` (_pyio.py:1052),
`raw.writable()` (:1248), `raw._checkSeekable()` (:1426, :430-435) first for a
`BufferedRandom`, and no `tell`. -/
def pyInitCalls : Nat → List RCall
  | 0 => [.readable]
  | 1 => [.writable]
  | _ => [.seekable, .readable, .writable]

/-- The raw after `calls`: each one logged and counted, nothing else changed (no
read, write or seek). -/
def afterCalls (raw : Raw) (calls : List RCall) : Raw :=
  calls.foldl (fun r c => { r with tick := r.tick + 1, log := r.log ++ [c] }) raw

/-- `io.BufferedReader(raw, size)` (`kind` 0), `BufferedWriter` (1) and
`BufferedRandom` (2), C twin, over a raw stream whose inquiries answer `True`:

1. `size <= 0` is refused with `ValueError("buffer size must be strictly
   positive")` (`_buffered_init`, :841-845), after the inquiries;
2. a buffer the allocator refuses (in the model, `size >= memLimit`: the module's
   allocation assumption, `PyIO/Basic.lean`, about the machine and not CPython) is
   refused with `MemoryError` (:848-851); the new lock is assumed allocated (the
   `RuntimeError` of :855-858 is not modelled);
3. otherwise the construction succeeds and sets what the body sets: `ok`, the raw
   attached and not detached, `buffer_size` = `size`, a buffer of `size` bytes, a
   free lock, `buffer_mask` = `size - 1` for a power of two and 0 otherwise
   (:863-868), `abs_pos` from the raw's `tell()` when it fits `Py_off_t` (:869-870; a
   failed `_buffered_raw_tell` is cleared and leaves the zeroed 0), an empty read
   buffer for a reader (`_bufferedreader_reset_buf`, `read_end` -1) and an empty
   write buffer at 0 for a writer (`_bufferedwriter_reset_buf`, `pos` 0); the raw has
   seen exactly `cInitCalls kind`.

Every hypothesis is the stated honest raw or the constructor's documented argument;
`kind ≤ 2` names the three types. -/
def CInitSucceeds : Prop := ∀ (kind : Nat) (raw : Raw) (size : Int), kind ≤ 2 → HonestRaw raw →
  (size ≤ 0 → runC kind raw size [] = .initErr (.valueError "buffer size must be strictly positive")) ∧
  (size ≥ memLimit → runC kind raw size [] = .initErr memoryError) ∧
  (0 < size → size < memLimit → ∃ s, runC kind raw size [] = .done s [] ∧
    s.ok = true ∧ s.detached = false ∧ s.rawNull = false ∧ s.locked = false ∧
    s.size = size ∧ s.hasBuf = true ∧ s.buffer.length = size.toNat ∧
    s.mask = (if size.toNat &&& (size.toNat - 1) = 0 then size.toNat - 1 else 0) ∧
    s.absPos = (if InSsize raw.pos then (raw.pos : Int) else 0) ∧
    (kind ≠ 1 → s.readEnd = -1) ∧ (kind ≠ 0 → s.writePos = 0 ∧ s.writeEnd = -1 ∧ s.pos = 0) ∧
    s.raw = afterCalls raw (cInitCalls kind))

/-- `_pyio.BufferedReader(raw, size)`, `BufferedWriter`, `BufferedRandom` over the
same raw streams: `size <= 0` is refused with `ValueError("invalid buffer size")`
(_pyio.py:1056-1057, :1252-1253), after the inquiry; every positive size is accepted
(nothing is allocated, so no `MemoryError`), and the object is attached, its
`buffer_size` is `size`, a reader's read buffer is empty at 0 with a free
`_read_lock` (:1058-1060, `_reset_read_buf` :1065-1067), a writer's write buffer is
empty with a free `_write_lock` (:1254-1256); the raw has seen exactly
`pyInitCalls kind` (its call counter restarts at 0: the harness arms its hooks once
the constructor has returned). -/
def PyInitSucceeds : Prop := ∀ (kind : Nat) (raw : Raw) (size : Int), kind ≤ 2 → HonestRaw raw →
  (size ≤ 0 → runP kind raw size [] = .initErr (.valueError "invalid buffer size")) ∧
  (0 < size → ∃ s, runP kind raw size [] = .done s [] ∧
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
    | (intro _; exact ⟨rfl, rfl, rfl⟩)
    | simp [afterCalls, cInitCalls, pyInitCalls]
    | (simp [afterCalls, cInitCalls, pyInitCalls]; done))

theorem cInitSucceeds_proven : CInitSucceeds := by
  intro kind raw size hk h
  obtain ⟨data, pos, rs, ws, ss, excMro, cs, qs, fr, cr, cw, csk, closed, cf, hooks, tick, log⟩ := raw
  obtain ⟨hq, hh, hs, hr, hw, hsk, hc⟩ := h
  dsimp only at hq hh hs hr hw hsk hc
  subst hq hh hs hr hw hsk hc
  refine ⟨fun h1 => ?_, fun h1 => ?_, fun h1 h2 => ?_⟩
  · rcases kind with _ | _ | _ | k
    all_goals first
      | omega
      | (unfold runC BC2.init; simp only [h1, ↓reduceIte]; rfl)
  · have hm : (0 : Int) < (memLimit : Int) := by decide
    have h0 : ¬ size ≤ 0 := by omega
    rcases kind with _ | _ | _ | k
    all_goals first
      | omega
      | (unfold runC BC2.init; simp only [h0, h1, ↓reduceIte]; rfl)
  · have h0 : ¬ size ≤ 0 := by omega
    have h2' : ¬ size ≥ (memLimit : Int) := by omega
    have hn : ¬ ((pos : Int) < 0) := by omega
    by_cases hp : InSsize (pos : Int)
    all_goals
      obtain rfl | rfl | rfl : kind = 0 ∨ kind = 1 ∨ kind = 2 := by omega
      all_goals first
        | (simp (config := { decide := true }) only [runC, BC2.init, BC2.bind_def, BC2.mod, BC2.get, BC2.put, BC2.thr, BC2.pure_apply,
             BC2.inquiryObj, BC2.onRawObj, BC2.callback, BC2.ofPy, BC2.checkInq, BC2.attempt,
             BC2.rawTell, BC2.onRaw, BC2.checkPos, BC2.asOff, Raw.enter, Raw.inquire, Raw.tell,
             Raw.popS, List.find?, Option.map, h0, h2', hp, hn, ↓reduceIte]
           refine ⟨_, rfl, ?_⟩
           refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
           init_fields)

theorem pyInitSucceeds_proven : PyInitSucceeds := by
  intro kind raw size hk h
  obtain ⟨data, pos, rs, ws, ss, excMro, cs, qs, fr, cr, cw, csk, closed, cf, hooks, tick, log⟩ := raw
  obtain ⟨hq, hh, hs, hr, hw, hsk, hc⟩ := h
  dsimp only at hq hh hs hr hw hsk hc
  subst hq hh hs hr hw hsk hc
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · rcases kind with _ | _ | _ | k
    all_goals first
      | omega
      | (unfold runP BP2.init; simp only [h1, ↓reduceIte]; rfl)
  · have h0 : ¬ size ≤ 0 := by omega
    rcases kind with _ | _ | _ | k
    all_goals first
      | omega
      | (unfold runP BP2.init
         simp only [h0, ↓reduceIte]
         refine ⟨_, rfl, ?_⟩
         refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
         init_fields)

end PyLean.PyIO
