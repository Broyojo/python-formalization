import PyLean.Pickle.DecSim

/-!
Payloads above 1 MiB and the end of a frame: `load_counted_binbytes` reads in
chunks, and each chunk is its own `_Unpickler_ReadInto`, whose check for a read
that crosses the end of a frame only sees that chunk.
-/

namespace PyLean.Pickle

open PyLean

/-- The state of each unpickler just after the opcode `BINBYTES` of a frame that
ends after `a`, with `b` outside it. -/
def chunkC (a b : Bytes) : CSt :=
  let data := leBytes (a.length + b.length) 4 ++ a ++ b
  { inp := data, idx := 0, inputLen := 4 + a.length, frameEnd := some (4 + a.length),
    savedInputLen := data.length }

def chunkPy (a b : Bytes) : PySt :=
  { inp := leBytes (a.length + b.length) 4 ++ a ++ b, pos := 4 + a.length,
    frame := some (leBytes (a.length + b.length) 4 ++ a, 0) }

/-- A `BINBYTES` payload that runs past the end of its frame is rejected, in both
unpicklers, wherever the frame ends: C's `_Unpickler_LeaveFrame` check and
`_Unframer.read` (`Lib/pickle.py:284-295`), which raises `pickle exhausted before
end of frame`. Through 3.14 the C read was one call. -/
def FrameChunkTwins : Prop :=
  ∀ a b : Bytes, a ≠ [] → b ≠ [] → a.length + b.length < 2 ^ 32 →
    isErr ((cLoadCountedBinbytes 4).run (chunkC a b)) = true ∧ isErr (pyLoadBinbytes.run (chunkPy a b)) = true

/-- A read that fits in what the frame or the buffer still holds. -/
theorem cReadInto_fit (c : CSt) (n : Nat) (hn : 0 < n) (hle : c.idx + n ≤ c.inputLen)
    (hl : c.inputLen ≤ c.inp.length) :
    (cReadInto n).run c = .ok ((c.inp.drop c.idx).take n, { c with idx := c.idx + n }) := by
  have h0 : c.inputLen - c.idx > 0 := by omega
  have hmin : min (c.inputLen - c.idx) n = n := by omega
  have hlen : ((c.inp.drop c.idx).take n).length = n := by
    rw [List.length_take, List.length_drop]; omega
  simp only [StateT.run, cReadInto, Bind.bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get,
    StateT.get, set, MonadStateOf.set, StateT.set, pure, Except.pure, StateT.pure]
  simp only [if_pos h0, hmin, hlen]
  rw [if_pos ⟨h0, trivial⟩]
  rfl

/-- A read that starts where the frame ends leaves the frame without an error. -/
theorem cReadInto_at_end (c : CSt) (n fe : Nat) (hn : 0 < n) (h0 : c.inputLen ≤ c.idx)
    (hf : c.frameEnd = some fe) (hle : c.idx + n ≤ c.savedInputLen) (hl : c.savedInputLen ≤ c.inp.length) :
    (cReadInto n).run c = .ok ((c.inp.drop c.idx).take n,
      { c with inputLen := c.savedInputLen, frameEnd := none, idx := c.idx + n }) := by
  have hz : c.inputLen - c.idx = 0 := by omega
  have hmin : min (c.savedInputLen - c.idx) n = n := by omega
  have hlen : ((c.inp.drop c.idx).take n).length = n := by
    rw [List.length_take, List.length_drop]; omega
  have hp : c.savedInputLen - c.idx > 0 := by omega
  obtain ⟨inp, idx, inputLen, frameEnd, saved, stack, marks, memo, memoSize, memoLen, memoDict, heap, proto⟩ := c
  simp only at h0 hf hle hl hz hmin hlen hp ⊢
  subst hf
  simp only [StateT.run, cReadInto, cLeaveFrame, Bind.bind, StateT.bind, Except.bind, get, getThe,
    MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set, pure, Except.pure, StateT.pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
  have h3 : min n (inp.length - idx) = n := by omega
  simp [hz, hmin, hlen, hp, h3, StateT.bind, StateT.modifyGet, StateT.get, StateT.set, StateT.pure,
    Except.bind, pure, Except.pure, bind]

/-- `cLoadCountedBinbytes` once its size is read. -/
theorem cBinbytes_run {c c' : CSt} {b : Bytes} {size : Nat} (hread : (cRead 4).run c = .ok (b, c'))
    (hb : calcBinsize b = some size) :
    (cLoadCountedBinbytes 4).run c =
      (cReadChunks (size + 1) size (min size cMinReadBufSize) 0 [] >>= fun d => cPush (.bytes d)).run c' := by
  unfold cLoadCountedBinbytes
  rw [cRun_bind, hread]
  dsimp only
  rw [hb]

theorem cReadChunks_succ (fuel size cursize prevsize : Nat) (acc : Bytes) :
    cReadChunks (fuel + 1) size cursize prevsize acc = (do
      let d ← cReadInto (cursize - prevsize)
      if cursize ≥ size then return acc ++ d
      else cReadChunks fuel size (cursize + min cursize (size - cursize)) cursize (acc ++ d)) := rfl

/-- Two chunks of `K` bytes from a frame that holds exactly the first. -/
theorem chunks_two (K fuel size : Nat) (hK : 0 < K) (hfuel : 2 ≤ fuel) (hsize : size = 2 * K) (c : CSt)
    (fe : Nat) (hf : c.frameEnd = some fe)
    (h1 : c.idx + K = c.inputLen) (hl : c.inputLen ≤ c.inp.length) (h2 : c.inputLen + K ≤ c.savedInputLen)
    (hl2 : c.savedInputLen ≤ c.inp.length) :
    ∃ r, (cReadChunks fuel size K 0 []).run c = .ok r := by
  subst hsize
  obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 2 := ⟨fuel - 2, by omega⟩
  rw [show g + 2 = (g + 1) + 1 from rfl, cReadChunks_succ, cRun_bind, Nat.sub_zero,
    cReadInto_fit c K hK (by omega) hl]
  dsimp only
  rw [if_neg (by omega), cReadChunks_succ, cRun_bind]
  have e1 : K + min K (2 * K - K) - K = K := by omega
  have e2 : K + min K (2 * K - K) = 2 * K := by omega
  rw [e1, cReadInto_at_end { c with idx := c.idx + K } K fe hK (by dsimp only; omega) hf
    (by dsimp only; omega) hl2]
  dsimp only
  rw [e2, if_pos (Nat.le_refl _)]
  exact ⟨_, rfl⟩

/-- The run on a frame that ends after `a`, with `a` and `b` of one chunk each. -/
theorem chunk_accepted (a b : Bytes) (K : Nat) (hK : 0 < K) (hK2 : min (2 * K) cMinReadBufSize = K)
    (hal : a.length = K) (hbl : b.length = K)
    (hb : calcBinsize (leBytes (2 * K) 4) = some (2 * K)) :
    isErr ((cLoadCountedBinbytes 4).run (chunkC a b)) = false := by
  have hsz : a.length + b.length = 2 * K := by omega
  have hle : (chunkC a b).idx + 4 ≤ (chunkC a b).inputLen := by
    show 0 + 4 ≤ 4 + a.length
    omega
  have e : ((chunkC a b).inp.drop (chunkC a b).idx).take 4 = leBytes (2 * K) 4 := by
    show ((leBytes (a.length + b.length) 4 ++ a ++ b).drop 0).take 4 = _
    rw [hsz, List.drop_zero, List.append_assoc]
    exact List.take_left' (leBytes_length _ 4)
  have hread : (cRead 4).run (chunkC a b) =
      .ok (leBytes (2 * K) 4, { chunkC a b with idx := (chunkC a b).idx + 4 }) := by
    rw [cRead_fast _ _ hle, e]
  rw [cBinbytes_run hread hb, hK2]
  have hdl : (chunkC a b).inp.length = 4 + a.length + b.length := by
    show (leBytes (a.length + b.length) 4 ++ a ++ b).length = _
    simp only [List.length_append, leBytes_length]
  obtain ⟨⟨d, s⟩, hr⟩ := chunks_two K (2 * K + 1) (2 * K) hK (by omega) rfl
    { chunkC a b with idx := (chunkC a b).idx + 4 } (4 + a.length) rfl
    (by show 0 + 4 + K = 4 + a.length; omega)
    (by show 4 + a.length ≤ (chunkC a b).inp.length; omega)
    (by show 4 + a.length + K ≤ (chunkC a b).inp.length; omega)
    (Nat.le_refl _)
  rw [cRun_bind, hr]
  rfl

/-- A 2 MiB `BINBYTES` whose frame ends after the first 1 MiB. The first chunk uses
the frame up, so the second starts with nothing in the buffer, and
`_Unpickler_LeaveFrame` sees no crossing. Python's `_Unframer.read` raises. -/
theorem frameChunkTwins_refuted : ¬ FrameChunkTwins := by
  intro h
  generalize ha : List.replicate 1048576 (0 : UInt8) = a
  have hal : a.length = 1048576 := by rw [← ha, List.length_replicate]
  have hkp : a ≠ [] := by
    intro e
    rw [e] at hal
    exact absurd hal (by decide)
  have hsz : a.length + a.length < 2 ^ 32 := by rw [hal]; decide
  have hc := (h a a hkp hkp hsz).1
  have hok := chunk_accepted a a 1048576 (by decide) (by decide +kernel) hal hal (by decide +kernel)
  exact absurd (hok.symm.trans hc) (by decide)

end PyLean.Pickle
