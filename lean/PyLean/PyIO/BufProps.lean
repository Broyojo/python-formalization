import PyLean.PyIO.BufOps

/-! Properties of `BufferedReader`/`Writer`/`Random` (`Modules/_io/bufferedio.c`
and `Lib/_pyio.py`), over the raw stream of `PyIO/BufRaw.lean`. -/

namespace PyLean.PyIO

open PyLean

/-- A seekable raw stream over `d` that follows its contract: no scripted short
reads, blocking, bad counts, exceptions, lies about `closed`, or re-entry. -/
def plainRaw (d : List Nat) : Raw :=
  { data := d, pos := 0, rs := [], ws := [], ss := [], cs := [], canRead := true, canWrite := true,
    canSeek := true, closed := false, closeFail := none, hooks := [], tick := 0, log := [] }

/-- The result of the last operation of a case, or what stopped the case. -/
def lastResult {σ : Type} : Outcome σ → Py Val
  | .done _ rs => rs.getLastD (.ok .none)
  | .initErr e => .error e
  | .crashed => .error crashErr
  | .hung => .error hangErr

/-- `read(k)` then `readinto(bytearray(n))` on a new `BufferedReader(raw, size)`,
C twin. -/
def cReadThenInto (d : List Nat) (size : Int) (k n : Nat) : Py Val :=
  lastResult (runC 0 (plainRaw d) size [.read (some k), .readinto n])

/-- The same two calls on `_pyio.BufferedReader`. -/
def pyReadThenInto (d : List Nat) (size : Int) (k n : Nat) : Py Val :=
  lastResult (runP 0 (plainRaw d) size [.read (some k), .readinto n])

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

theorem bind_def {α β : Type} (m : PM α) (f : α → PM β) (R : PH) (s : BufP) :
    (m >>= f) R s = match m R s with
      | (s', .ok a) => f a R s'
      | (s', .error e) => (s', .error e) := rfl

theorem pure_def {α : Type} (a : α) (R : PH) (s : BufP) : (pure a : PM α) R s = (s, .ok a) := rfl

/-- What `with lock:` returns is what its body returned, from some state. -/
theorem withLock_ok {α : Type} (w : Bool) (m : PM α) (R : PH) (s s' : BufP) (v : α)
    (h : withLock w m R s = (s', .ok v)) : ∃ s1 s2, m R s1 = (s2, .ok v) := by
  unfold withLock at h
  by_cases hc : (if w then s.wl else s.rl) = true
  · rw [if_pos hc] at h; simp at h
  · rw [if_neg hc] at h
    generalize hm : m R (if w then { s with wl := true } else { s with rl := true }) = p at h
    obtain ⟨s2, r⟩ := p
    simp only [Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨_, _, hm⟩

theorem readMore_nodata (n : Int) (wanted : Nat) (R : PH) : ∀ (fuel : Nat) (chunks : List Nat) (avail : Int)
    (s s' : BufP) (r : List Nat × Int × Option (List Nat)),
    readMore n wanted fuel chunks avail R s = (s', .ok r) → r.2.2 = none ∨ r.2.2 = some [] := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ h; simp [readMore, thr] at h
  | succ f ih =>
    intro chunks avail s s' r h
    simp only [readMore] at h
    split at h
    · rw [bind_def] at h
      rcases hr : rawRead wanted true R s with ⟨s1, r1⟩
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
theorem readUnlocked_le (n : Nat) (R : PH) (s s' : BufP) (r : Option (List Nat)) (d : List Nat)
    (h : readUnlocked n R s = (s', .ok r)) (hd : r = some d) : d.length ≤ n := by
  subst hd
  have hne : ¬ ((n : Int) = -1) := by omega
  simp only [readUnlocked] at h
  rw [bind_def] at h
  simp only [get, hne, ite_false] at h
  split at h
  · rw [bind_def] at h
    simp only [mod, pure_def, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp; omega
  · rw [bind_def] at h
    split at h
    · next s1 a hm =>
      obtain ⟨out, av, nd⟩ := a
      have hnd := readMore_nodata _ _ _ _ _ _ _ _ _ hm
      simp only at h
      rw [bind_def] at h
      simp only [mod] at h
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

theorem read_le (n : Nat) (R : PH) (s s' : BufP) (v : Val) (h : read (some (n : Int)) R s = (s', .ok v)) :
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
      obtain ⟨s3, s4, hu⟩ := withLock_ok _ _ _ _ _ _ hr
      cases r with
      | none => simp [optBytes, Val.bytesOf, Val.none]
      | some d => simpa [optBytes, Val.bytesOf, Val.bytes] using readUnlocked_le n _ _ _ _ d hu rfl
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
theorem readlineLoop_le (size : Int) (hs : 0 ≤ size) (R : PH) : ∀ (fuel : Nat) (res : List Nat) (s s' : BufP)
    (v : List Nat), (res.length : Int) ≤ size → readlineLoop size fuel res R s = (s', .ok v) →
    (v.length : Int) ≤ size := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ h; simp [readlineLoop, thr] at h
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
          have hb' := read_le _ _ _ _ _ hb
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
never returns more than `size` bytes, for every raw stream (scripted, lying, or
re-entering the object) and every state of the buffer ("at most size bytes will be
read", _pyio.py:516). `IOBase.readline` is what runs here, and its `peek` branch is
what 3.15 corrected. A failing call returns nothing to bound. -/
def PyBufferedReadlineBound : Prop := ∀ (R : PH) (s s' : BufP) (size : Int) (v : Val), 0 ≤ size →
  BP2.stepOp (.readline (some size)) R s = (s', .ok v) → (v.bytesOf.length : Int) ≤ size

theorem pyBufferedReadlineBound_proven : PyBufferedReadlineBound := by
  intro R s s' size v hs h
  simp only [BP2.stepOp, BP2.bind_def, BP2.get] at h
  by_cases hk : s.kind = 1
  · -- a writer: `IOBase.readline` returns `b""` for size 0 and raises otherwise
    simp only [hk, ite_true] at h
    split at h
    · simp only [BP2.pure_def, Prod.mk.injEq, Except.ok.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp [Val.bytesOf]; omega
    · simp [BP2.thr] at h
  simp only [hk, ite_false, BP2.bind_def] at h
  split at h
  · next s1 r hr =>
    simp only [BP2.pure_def, Prod.mk.injEq, Except.ok.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp only [BP2.readlineRaw, Option.getD_some, BP2.bind_def, BP2.get] at hr
    simpa [Val.bytesOf, Val.bytes] using BP2.readlineLoop_le size hs R _ [] _ _ _ (by simpa using hs) hr
  · simp at h

end PyLean.PyIO
