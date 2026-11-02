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

/-! ## `IOBase.readline(size)` over `_pyio.BufferedReader` -/

namespace BP2

theorem bind_def {σ α β : Type} (m : SM σ α) (f : α → SM σ β) (s : σ) :
    (m >>= f) s = match m s with
      | (s', .ok a) => f a s'
      | (s', .error e) => (s', .error e) := rfl

theorem pure_def {σ α : Type} (a : α) (s : σ) : (pure a : SM σ α) s = (s, .ok a) := rfl

theorem readMore_nodata (n : Int) (wanted : Nat) : ∀ (fuel : Nat) (chunks : List Nat) (avail : Int)
    (s s' : BufP) (r : List Nat × Int × Option (List Nat)),
    readMore n wanted fuel chunks avail s = (s', .ok r) → r.2.2 = none ∨ r.2.2 = some [] := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ h; simp [readMore, SM.thr] at h
  | succ f ih =>
    intro chunks avail s s' r h
    simp only [readMore] at h
    split at h
    · rw [bind_def] at h
      rcases hr : rawRead wanted s with ⟨s1, r1⟩
      rw [hr] at h
      cases r1 with
      | error e => simp at h
      | ok c =>
        simp only at h
        cases c with
        | none => simp only [pure_def, Prod.mk.injEq, Except.ok.injEq] at h; obtain ⟨-, rfl⟩ := h; simp
        | some d =>
          simp only at h
          split at h
          · simp only [pure_def, Prod.mk.injEq, Except.ok.injEq] at h; obtain ⟨-, rfl⟩ := h; simp
          · exact ih _ _ _ _ _ h
    · simp only [pure_def, Prod.mk.injEq, Except.ok.injEq] at h; obtain ⟨-, rfl⟩ := h; simp

/-- `_read_unlocked(n)` never hands back more than `n` bytes. -/
theorem readUnlocked_le (n : Nat) (s s' : BufP) (r : Option (List Nat)) (d : List Nat)
    (h : readUnlocked n s = (s', .ok r)) (hd : r = some d) : d.length ≤ n := by
  subst hd
  have hne : ¬ ((n : Int) = -1) := by omega
  simp only [readUnlocked] at h
  rw [bind_def] at h
  simp only [SM.get, hne, ite_false] at h
  split at h
  · rw [bind_def] at h
    simp only [SM.mod, pure_def, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp; omega
  · rw [bind_def] at h
    split at h
    · next s1 a hm =>
      obtain ⟨out, av, nd⟩ := a
      have hnd := readMore_nodata _ _ _ _ _ _ _ _ hm
      simp only at h
      rw [bind_def] at h
      simp only [SM.mod] at h
      split at h
      · simp only [pure_def, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at h
        obtain ⟨-, rfl⟩ := h
        simp only [List.length_take]
        omega
      · simp only [pure_def, Prod.mk.injEq, Except.ok.injEq] at h
        obtain ⟨-, rfl⟩ := h
        simp at hnd
        simp [hnd]
    · simp at h

theorem read_le (n : Nat) (s s' : BufP) (v : Val) (h : read (some (n : Int)) s = (s', .ok v)) :
    v.bytesOf.length ≤ n := by
  have hn : ¬ ((n : Int) < -1) := by omega
  simp only [read] at h
  rw [bind_def] at h
  split at h
  · simp only [Option.getD_some, hn, ite_false] at h
    rw [bind_def] at h
    split at h
    · next s2 r hr =>
      simp only [pure_def, Prod.mk.injEq, Except.ok.injEq] at h
      obtain ⟨-, rfl⟩ := h
      cases r with
      | none => simp [Val.bytesOf, Val.none]
      | some d => simpa [Val.bytesOf, Val.bytes] using readUnlocked_le n _ _ _ d hr rfl
    · simp at h
  · simp at h

theorem nreadahead_le (size : Int) (len : Nat) (ra : List Nat) (hs : 0 ≤ size) (h : (len : Int) < size) :
    (nreadahead size len ra : Int) ≤ size - len := by
  unfold nreadahead
  split
  · omega
  · simp only
    omega

/-- The loop of `IOBase.readline`: the line never outgrows `size`, because each read
asks for at most `size - len(res)` bytes and gets no more than it asked for. -/
theorem readlineLoop_le (size : Int) (hs : 0 ≤ size) : ∀ (fuel : Nat) (res : List Nat) (s s' : BufP)
    (v : List Nat), (res.length : Int) ≤ size → readlineLoop size fuel res s = (s', .ok v) →
    (v.length : Int) ≤ size := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ h; simp [readlineLoop, SM.thr] at h
  | succ f ih =>
    intro res s s' v hr h
    simp only [readlineLoop] at h
    split at h
    · next hc =>
      have hlt : (res.length : Int) < size := by omega
      rw [bind_def] at h
      split at h
      · next s1 r _ =>
        rw [bind_def] at h
        split at h
        · next s2 b hb =>
          have hb' := read_le _ _ _ _ hb
          split at h
          · simp only [pure_def, Prod.mk.injEq, Except.ok.injEq] at h
            obtain ⟨-, rfl⟩ := h
            exact hr
          · have hn := nreadahead_le size res.length r.bytesOf hs hlt
            have hlen : ((res ++ b.bytesOf).length : Int) ≤ size := by
              simp only [List.length_append]
              omega
            split at h
            · simp only [pure_def, Prod.mk.injEq, Except.ok.injEq] at h
              obtain ⟨-, rfl⟩ := h
              exact hlen
            · exact ih _ _ _ _ hlen h
        · simp at h
      · simp at h
    · simp only [pure_def, Prod.mk.injEq, Except.ok.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact hr

end BP2

/-- `readline(size)` with `size >= 0` on a `_pyio.BufferedReader` or `BufferedRandom`
never returns more than `size` bytes, for every raw stream and every state of the
buffer ("at most size bytes will be read", _pyio.py:516). `IOBase.readline` is what
runs here, and its `peek` branch is what 3.15 corrected. A failing call returns
nothing to bound. -/
def PyBufferedReadlineBound : Prop := ∀ (s s' : BufP) (size : Int) (v : Val), 0 ≤ size →
  BP2.stepOp s (.readline (some size)) = (s', .ok v) → (v.bytesOf.length : Int) ≤ size

theorem pyBufferedReadlineBound_proven : PyBufferedReadlineBound := by
  intro s s' size v hs h
  simp only [BP2.stepOp] at h
  rw [BP2.bind_def] at h
  split at h
  · next s1 r hr =>
    simp only [BP2.pure_def, Prod.mk.injEq, Except.ok.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp only [BP2.readlineRaw, Option.getD_some] at hr
    rw [BP2.bind_def] at hr
    simpa [Val.bytesOf, Val.bytes] using BP2.readlineLoop_le size hs _ [] _ _ _ (by simpa using hs) hr
  · simp at h

end PyLean.PyIO
