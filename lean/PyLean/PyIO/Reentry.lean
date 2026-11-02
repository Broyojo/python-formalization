import PyLean.PyIO.BytesExtra
import PyLean.PyIO.StringExtra

/-!
What 3.15 changed in the in-memory streams: a failed `BytesIO.write` no longer
closes the stream, `truncate` converts its argument where Python code can run in
the middle of the method, a refused `__init__` leaves the stream alone, and
`readinto` may read from the view it writes into.
-/

namespace PyLean.PyIO

open PyLean

/-! ## A failed `BytesIO.write` -/

/-- On an open `io.BytesIO` with no views, a non-empty write succeeds while its end
fits the buffer or the allocation bound. Beyond them it fails and the stream is as
it was: open, with the same contents and position, whether or not the buffer was
shared (`_PyBytes_ResizeKeepOnError` and `unshare_buffer_lock_held` both keep it).
The hypotheses are the states in which `write` reaches the resize: the closed and
exported refusals come first. -/
def BytesIOWriteFailureKeeps : Prop := ∀ (s : BState) (b : List Nat),
  s.closed = false → s.exports = 0 → b ≠ [] →
  ((s.pos + b.length ≤ s.buf.length ∨ s.pos + b.length < memLimit) →
    (C.write s b).2 = .ok (.int b.length)) ∧
  (s.buf.length < s.pos + b.length → memLimit ≤ s.pos + b.length →
    (C.write s b).1 = s ∧ (C.write s b).2.toBool = false ∧
    (C.step (C.write s b).1 .getvalue).2 = .ok (.bytes s.buf) ∧
    (C.step (C.write s b).1 .closed).2 = .ok (.bool false))

theorem bytesIOWriteFailureKeeps_proven : BytesIOWriteFailureKeeps := by
  intro s b hc he hb
  have hmax : memLimit ≤ ssizeMax := by decide
  have hl : b.length ≠ 0 := fun h => hb (List.eq_nil_of_length_eq_zero h)
  have he' : ¬ s.exports > 0 := by omega
  constructor
  · intro h
    have c1 : ¬ (s.pos + b.length > s.buf.length ∧ ((s.pos + b.length : Nat) : Int) > ssizeMax) := by omega
    have c2 : ¬ (s.pos + b.length > s.buf.length ∧ ((s.pos + b.length : Nat) : Int) = ssizeMax) := by omega
    have c3 : ¬ (s.pos + b.length > s.buf.length ∧ s.pos + b.length ≥ memLimit) := by omega
    simp only [C.write, hc, Bool.false_eq_true, ite_false, he', hl, c1, c2, c3]
  · intro h1 h2
    have c3 : s.pos + b.length > s.buf.length ∧ s.pos + b.length ≥ memLimit := ⟨h1, h2⟩
    have hw : ∃ e, C.write s b = (s, .error e) := by
      simp only [C.write, hc, Bool.false_eq_true, ite_false, he', hl, c3, and_self, ite_true]
      split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
    obtain ⟨e, hw⟩ := hw
    rw [hw]
    simp [C.step, hc, Except.toBool]

/-! ## `truncate` -/

/-- `truncate(v)` with an int `v >= 0` cuts the contents to `v` and returns `v`, on
an open stream (C and Python `BytesIO`, with no views; C `StringIO`). A closed
stream refuses whatever the argument, in both C types: the stream is checked before
the argument is converted, so an `int` too large for C does not change the error
(C `StringIO` converted it first until 3.15). -/
def TruncateResult : Prop := ∀ (s : BState) (t : SCState) (v : Int), 0 ≤ v →
  (s.closed = false → s.exports = 0 → InSsize v →
    C.truncate s (some v) = ({ s with buf := s.buf.take v.toNat }, .ok (.int v))) ∧
  (s.closed = false → s.exports = 0 →
    P.truncate s (some v) = ({ s with buf := s.buf.take v.toNat }, .ok (.int v))) ∧
  (t.closed = false → InSsize v →
    SC.step t (.truncate (some v)) = ({ t with buf := t.buf.take v.toNat }, .ok (.int v))) ∧
  (s.closed = true → C.truncate s (some v) = (s, .error C.closedErr)) ∧
  (t.closed = true → SC.step t (.truncate (some v)) = (t, .error SC.closedErr))

theorem take_toNat_eq (l : List Nat) (v : Int) (h : ¬ v < l.length) : l.take v.toNat = l :=
  List.take_of_length_le (by omega)

theorem truncateResult_proven : TruncateResult := by
  intro s t v hv
  have hn : ¬ v < 0 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hc he hr
    have he' : ¬ s.exports > 0 := by omega
    by_cases hl : v < s.buf.length
    · simp [C.truncate, hc, he', asLong, hr, hn, hl]
    · simp [C.truncate, hc, he', asLong, hr, hn, hl, take_toNat_eq _ _ hl]
      cases s; simp_all
  · intro hc he
    have he' : ¬ s.exports > 0 := by omega
    by_cases hl : v < s.buf.length
    · simp [P.truncate, hc, he', hn, hl]
    · simp [P.truncate, hc, hn, hl, take_toNat_eq _ _ hl]
      cases s; simp_all
  · intro hc hr
    by_cases hl : v < t.buf.length
    · simp [SC.step, hc, asLong, hr, hn, hl]
    · simp [SC.step, hc, asLong, hr, hn, hl, take_toNat_eq _ _ hl]
      cases t; simp_all
  · intro hc; simp [C.truncate, hc]
  · intro hc; simp [SC.step, hc]

/-- With an object whose `__index__` runs `hook` and returns `v`, `io.BytesIO.truncate`
looks at the stream again: if the hook closed it the call raises `ValueError`, if the
hook left a view alive it raises `BufferError`, and only otherwise does it cut the
contents. With nothing in the hook it is `truncate(v)`. The hypotheses are the state
in which the first checks pass and an index that converts: the other outcomes are
the failure paths of `C.truncateObj` before the re-check. -/
def BytesIOTruncateRecheck : Prop := ∀ (s : BState) (hook : List Hook) (v : Int),
  s.closed = false → s.exports = 0 → InSsize v → 0 ≤ v →
  C.truncateObj s (.index [] (some v)) = C.truncate s (some v) ∧
  let s' := hook.foldl C.hookStep s
  (s'.closed = true → C.truncateObj s (.index hook (some v)) = (s', .error C.closedErr)) ∧
  (s'.closed = false → s'.exports > 0 → C.truncateObj s (.index hook (some v)) = (s', .error bufferError)) ∧
  (s'.closed = false → s'.exports = 0 →
    (C.truncateObj s (.index hook (some v))).2 = .ok (.int v) ∧
    (C.truncateObj s (.index hook (some v))).1.buf = s'.buf.take v.toNat)

theorem bytesIOTruncateRecheck_proven : BytesIOTruncateRecheck := by
  intro s hook v hc he hr hv
  have hn : ¬ v < 0 := by omega
  have he' : ¬ s.exports > 0 := by omega
  refine ⟨by simp [C.truncateObj, C.truncate, hc, he', asLong, hr, hn], ?_⟩
  intro s'
  have hs' : hook.foldl C.hookStep s = s' := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro h; simp [C.truncateObj, hc, he', asLong, hr, hn, hs', h]
  · intro h1 h2; simp [C.truncateObj, hc, he', asLong, hr, hn, hs', h1, h2]
  · intro h1 h2
    have h2' : ¬ s'.exports > 0 := by omega
    by_cases hl : v < s'.buf.length
    · simp [C.truncateObj, hc, he', asLong, hr, hn, hs', h1, h2', hl]
    · simp [C.truncateObj, hc, he', asLong, hr, hn, hs', h1, h2', hl, take_toNat_eq _ _ hl]

/-- For every object and every stream, `truncate` agrees between the `BytesIO` twins
up to the exception class. -/
def BytesIOTruncateIndexTwins : Prop := ∀ (s : BState) (a : TArg),
  sameClass (C.truncateObj s a).2 (P.truncateObj s a).2 = true

/-- `__index__` calling `seek(0, 1)`: C returns, while `_pyio` holds `self._lock`
across `__index__` and blocks on it forever. -/
theorem bytesIOTruncateIndexTwins_refuted : ¬BytesIOTruncateIndexTwins := by
  intro h
  have := h ⟨[97], 0, false, 0, false⟩ (.index [.seekCur] (some 0))
  revert this
  decide

/-- `truncate` of any object on a C `StringIO` does not kill the process. -/
def StringIOTruncateNoCrash : Prop := ∀ (accum : Bool) (s : SCState) (a : TArg),
  (SC.truncateObj accum s a).2 ≠ .error SC.segv

/-- `f = io.StringIO(); f.write('a'); f.truncate(x)`, where `x.__index__` closes `f`
and returns 0: the stream is still accumulating, `close` has cleared `self->writer`,
and `truncate` goes on to `realize`. -/
theorem stringIOTruncateNoCrash_refuted : ¬StringIOTruncateNoCrash := by
  intro h
  apply h true
    { buf := [97], pos := 1, closed := false, readnl := some [10], readuniversal := false
      readtranslate := false, writenl := none, hasDecoder := false, translate := false
      seennl := ⟨false, false, false⟩ }
    (.index [.close] (some 0))
  decide

/-- On a realized `StringIO`, `truncate` of any object ends in a result or an
exception. With nothing in the hook it is `truncate(v)`. -/
def StringIOTruncateRealized : Prop := ∀ (s : SCState) (a : TArg),
  (SC.truncateObj false s a).2 ≠ .error SC.segv ∧
  ∀ v, InSsize v → SC.truncateObj false s (.index [] (some v)) = SC.step s (.truncate (some v))

theorem stringIOTruncateRealized_proven : StringIOTruncateRealized := by
  intro s a
  constructor
  · unfold SC.truncateObj
    by_cases hc : s.closed = true
    · simp [hc, SC.closedErr, SC.segv]
    · simp only [hc, ite_false]
      cases a with
      | noIndex t r => simp [notIndexable, SC.segv]
      | index hook r =>
        cases r with
        | none => simp [boomErr, SC.segv]
        | some v =>
          by_cases hr : InSsize v
          · by_cases hn : v < 0 <;> simp [asLong, hr, hn, SC.segv]
          · simp [asLong, hr, SC.segv]
  · intro v hr
    by_cases h1 : s.closed = true <;> by_cases h2 : v < 0 <;>
      simp [SC.truncateObj, SC.step, asLong, hr, h1, h2, SC.sizeAfter]

/-! ## `__init__` called again -/

/-- A second `__init__` on an `io.BytesIO` with a live view raises `BufferError` and
changes nothing. With no views an initial value replaces the contents, rewinds and
reopens the stream, and with no initial value the contents and position are reset.
`_pyio.BytesIO.__init__` always succeeds on `bytes`, starting a new `bytearray`, and
leaves the closed flag alone. -/
def BytesIOReinit : Prop := ∀ (s : BState) (b : Option (List Nat)),
  (s.exports > 0 → C.xstep s (.reinit b) = (s, .error bufferError) ∧
    C.xstep s (.reinitObj b) = (s, .error bufferError)) ∧
  (s.exports = 0 → (C.xstep s (.reinit b)).2 = .ok .none ∧
    (C.xstep s (.reinit b)).1.buf = b.getD [] ∧ (C.xstep s (.reinit b)).1.pos = 0 ∧
    (C.xstep s (.reinit b)).1.closed = (b.isNone && s.closed)) ∧
  P.xstep s (.reinit b) = ({ s with buf := b.getD [], pos := 0, exports := 0 }, .ok .none)

theorem bytesIOReinit_proven : BytesIOReinit := by
  intro s b
  refine ⟨?_, ?_, rfl⟩
  · intro h; simp [C.xstep, C.reinit, C.reinitObj, h]
  · intro h
    have h' : ¬ s.exports > 0 := by omega
    cases b <;> simp [C.xstep, C.reinit, h']

/-! ## `readinto` from the stream's own buffer -/

theorem readintoSelf_open_C (buf : List Nat) (pos ex : Nat) (sh : Bool) (off n : Nat) :
    C.readintoSelf ⟨buf, pos, false, ex, sh⟩ off n =
      (⟨C.overwrite buf off (slice buf pos (readCount buf.length pos (min n (buf.length - off) : Nat))),
        pos + readCount buf.length pos (min n (buf.length - off) : Nat), false, ex,
        (C.takeView ⟨buf, pos, false, ex, sh⟩).shared⟩,
       .ok (.int (readCount buf.length pos (min n (buf.length - off) : Nat)))) := by
  unfold C.readintoSelf
  simp only [Bool.false_eq_true, ite_false]
  generalize hw : min n (buf.length - off) = w
  generalize hL : (if (w : Int) > (buf.length : Int) - pos then (buf.length : Int) - pos else (w : Int)) = L
  have hrc : L < 0 → readCount buf.length pos w = 0 := by
    intro h; unfold readCount; split <;> (try split) <;> (try split at hL) <;> omega
  have hrc2 : ¬ L < 0 → L = (readCount buf.length pos w : Int) := by
    intro h; unfold readCount; split <;> (try split) <;> split at hL <;> omega
  by_cases hneg : L < 0
  · simp [hneg, hrc hneg, slice, C.overwrite]
  · have e := hrc2 hneg
    have e2 : L.toNat = readCount buf.length pos w := by omega
    simp only [hneg, ite_false, e2]
    rw [e]

/-- `readinto` into a view of the stream's own buffer, with the two ranges free to
overlap: on an open stream both twins return the same count, end at the same position
and leave the same contents, which are the old contents at the read position copied
to the view. C copies with `memmove`; `_pyio` reads a copy first. -/
def BytesIOReadintoOverlap : Prop := ∀ (s : BState) (off n : Nat), s.closed = false →
  let k := readCount s.buf.length s.pos (min n (s.buf.length - off) : Nat)
  (C.readintoSelf s off n).2 = .ok (.int k) ∧ (P.readintoSelf s off n).2 = .ok (.int k) ∧
  (C.readintoSelf s off n).1.pos = s.pos + k ∧ (P.readintoSelf s off n).1.pos = s.pos + k ∧
  (C.readintoSelf s off n).1.buf = C.overwrite s.buf off (slice s.buf s.pos k) ∧
  (P.readintoSelf s off n).1.buf = C.overwrite s.buf off (slice s.buf s.pos k)

theorem bytesIOReadintoOverlap_proven : BytesIOReadintoOverlap := by
  intro s off n hc
  obtain ⟨buf, pos, cl, ex, sh⟩ := s
  simp only at hc; subst hc
  dsimp only
  have hC := readintoSelf_open_C buf pos ex sh off n
  have hP : P.readintoSelf ⟨buf, pos, false, ex, sh⟩ off n =
      (⟨C.overwrite buf off (slice buf pos (readCount buf.length pos (min n (buf.length - off) : Nat))),
        pos + readCount buf.length pos (min n (buf.length - off) : Nat), false, ex, sh⟩,
       .ok (.int (readCount buf.length pos (min n (buf.length - off) : Nat)))) := by
    have hle : readCount buf.length pos (min n (buf.length - off) : Nat) ≤ (buf.drop pos).length := by
      simp [readCount]; split <;> (try split) <;> omega
    unfold P.readintoSelf
    simp only [Bool.false_eq_true, ite_false]
    rw [P_read_open _ _ rfl]
    simp only [Option.getD_some, slice_length _ _ _ hle]
  rw [hC, hP]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end PyLean.PyIO
