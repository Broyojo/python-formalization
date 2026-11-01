import PyLean.PyIO.BytesSim

/-!
Documented invariants of the in-memory streams (`Doc/library/io.rst`,
"Binary I/O" / `BytesIO`, `IOBase.seek`/`truncate`), proven for both
`BytesIO` twins and, where they apply, the C `StringIO`.
-/

namespace PyLean.PyIO

open PyLean

/-! ## `writeAt` is "overwrite, zero-filling any gap" -/

theorem writeAt_length (buf b : List Nat) (pos : Nat) :
    (writeAt buf pos b).length = max buf.length (pos + b.length) := by
  unfold writeAt
  simp only [List.length_append, List.length_take, List.length_replicate, List.length_drop]
  omega

theorem writeAt_get (buf b : List Nat) (pos i : Nat) :
    (writeAt buf pos b)[i]? =
      if i < pos then (if i < buf.length then buf[i]? else some 0)
      else if i < pos + b.length then b[i - pos]? else buf[i]? := by
  unfold writeAt
  have hA : ((buf ++ List.replicate (pos - buf.length) 0).take pos).length = pos := by
    simp; omega
  by_cases h1 : i < pos
  · rw [List.append_assoc, List.getElem?_append_left (by rw [hA]; exact h1)]
    simp only [h1, ite_true, List.getElem?_take]
    by_cases h2 : i < buf.length
    · simp [h2, List.getElem?_append_left h2]
    · simp only [h2, ite_false]
      rw [List.getElem?_append_right (by omega), List.getElem?_replicate]
      simp; omega
  · rw [List.append_assoc, List.getElem?_append_right (by rw [hA]; omega), hA]
    simp only [h1, ite_false]
    by_cases h2 : i < pos + b.length
    · rw [List.getElem?_append_left (by omega)]; simp [h2]
    · rw [List.getElem?_append_right (by omega), List.getElem?_drop]
      simp only [h2, ite_false]
      congr 1; omega

/-- The documented effect of writing `b` at `pos` into `old`: the result is
`max(len(old), pos + len(b))` long, holds `b` at `pos`, keeps `old`
elsewhere and has zeros in any gap between `len(old)` and `pos`. -/
def ZeroFill (old : List Nat) (pos : Nat) (b new : List Nat) : Prop :=
  new.length = max old.length (pos + b.length) ∧
  ∀ i, new[i]? = if i < pos then (if i < old.length then old[i]? else some 0)
    else if i < pos + b.length then b[i - pos]? else old[i]?

theorem writeAt_zeroFill (buf b : List Nat) (pos : Nat) : ZeroFill buf pos b (writeAt buf pos b) :=
  ⟨writeAt_length buf b pos, writeAt_get buf b pos⟩

/-! ## The properties -/

theorem C_write_ok (s : BState) (b : List Nat) (v : Val) (h : (C.write s b).2 = .ok v) :
    v = .int b.length ∧ (C.write s b).1 =
      (if b = [] then s else { s with buf := writeAt s.buf s.pos b, pos := s.pos + b.length, shared := false }) := by
  unfold C.write at *
  dsimp only at h ⊢
  by_cases hc : s.closed = true
  · rw [if_pos hc] at h; simp at h
  rw [if_neg hc] at h ⊢
  by_cases he : s.exports > 0
  · rw [if_pos he] at h; simp at h
  rw [if_neg he] at h ⊢
  by_cases hb : b.length = 0
  · rw [if_pos hb] at h ⊢
    have : b = [] := List.eq_nil_of_length_eq_zero hb
    subst this; simp at h; simp; exact h.symm
  rw [if_neg hb] at h ⊢
  have hb' : b ≠ [] := fun e => hb (by simp [e])
  by_cases c1 : s.pos + b.length > s.buf.length ∧ ((s.pos + b.length : Nat) : Int) > ssizeMax
  · rw [if_pos c1] at h; simp at h
  rw [if_neg c1] at h ⊢
  by_cases c2 : s.pos + b.length > s.buf.length ∧ ((s.pos + b.length : Nat) : Int) = ssizeMax
  · rw [if_pos c2] at h; split at h <;> simp at h
  rw [if_neg c2] at h ⊢
  by_cases c3 : s.pos + b.length > s.buf.length ∧ s.pos + b.length ≥ memLimit
  · rw [if_pos c3] at h; split at h <;> simp at h
  rw [if_neg c3] at h ⊢
  simp at h
  simp [hb']; exact h.symm

theorem P_write_ok (s : BState) (b : List Nat) (v : Val) (h : (P.write s b).2 = .ok v) :
    v = .int b.length ∧ (P.write s b).1 =
      (if b = [] then s else { s with buf := writeAt s.buf s.pos b, pos := s.pos + b.length }) := by
  unfold P.write at *
  dsimp only at h ⊢
  by_cases hc : s.closed = true
  · rw [if_pos hc] at h; simp at h
  rw [if_neg hc] at h ⊢
  by_cases hb : b.length = 0
  · rw [if_pos hb] at h ⊢
    have : b = [] := List.eq_nil_of_length_eq_zero hb
    subst this; simp at h; simp; exact h.symm
  rw [if_neg hb] at h ⊢
  have hb' : b ≠ [] := fun e => hb (by simp [e])
  simp only [hb', ite_false]
  by_cases hp : s.pos > s.buf.length
  · rw [if_pos hp] at h ⊢
    by_cases d1 : (s.pos : Int) > ssizeMax
    · rw [if_pos d1] at h; simp at h
    rw [if_neg d1] at h ⊢
    by_cases d2 : s.exports > 0
    · rw [if_pos d2] at h; simp at h
    rw [if_neg d2] at h ⊢
    by_cases d3 : s.pos ≥ memLimit
    · rw [if_pos d3] at h; simp at h
    rw [if_neg d3] at h ⊢
    dsimp only at h ⊢
    have hl : (s.buf ++ List.replicate (s.pos - s.buf.length) 0).length = s.pos := by simp; omega
    rw [hl] at h ⊢
    have e1 : ¬ (s.pos + b.length > s.pos ∧ s.exports > 0) := fun h' => d2 h'.2
    rw [if_neg e1] at h ⊢
    by_cases e2 : s.pos + b.length > s.pos ∧ s.pos + b.length ≥ memLimit
    · rw [if_pos e2] at h; simp at h
    rw [if_neg e2] at h ⊢
    simp at h
    refine ⟨h.symm, ?_⟩
    simp [writeAt_pad _ _ _ hp]
  · rw [if_neg hp] at h ⊢
    dsimp only at h ⊢
    by_cases e1 : s.pos + b.length > s.buf.length ∧ s.exports > 0
    · rw [if_pos e1] at h; simp at h
    rw [if_neg e1] at h ⊢
    by_cases e2 : s.pos + b.length > s.buf.length ∧ s.pos + b.length ≥ memLimit
    · rw [if_pos e2] at h; simp at h
    rw [if_neg e2] at h ⊢
    simp at h
    exact ⟨h.symm, rfl⟩

/-- `write(b)` returns `len(b)` and advances the position by `len(b)`
whenever it succeeds (both BytesIO twins, every state and `b`). -/
def TellAfterWrite : Prop := ∀ (s : BState) (b : List Nat) (v : Val),
  ((C.write s b).2 = .ok v → v = .int b.length ∧ (C.write s b).1.pos = s.pos + b.length) ∧
  ((P.write s b).2 = .ok v → v = .int b.length ∧ (P.write s b).1.pos = s.pos + b.length)

theorem tellAfterWrite_proven : TellAfterWrite := by
  intro s b v
  constructor
  · intro h
    obtain ⟨hv, hs⟩ := C_write_ok s b v h
    refine ⟨hv, ?_⟩
    rw [hs]; split
    · next hb => subst hb; simp
    · rfl
  · intro h
    obtain ⟨hv, hs⟩ := P_write_ok s b v h
    refine ⟨hv, ?_⟩
    rw [hs]; split
    · next hb => subst hb; simp
    · rfl

/-- Reading after an absolute seek returns the matching slice of the
buffer: on an open stream, `seek(p)` then `read(n)` returns `buf[p:p+n]` for
all `p, n >= 0` (C: within `Py_ssize_t`) — for both BytesIO twins and the C
StringIO. -/
def ReadAfterSeek : Prop :=
  ∀ (s : BState) (t : SCState) (p n : Int), s.closed = false → t.closed = false → 0 ≤ p → 0 ≤ n →
  (InSsize p → InSsize n →
    (C.read (C.seek s p 0).1 (some n)).2 = .ok (.bytes (slice s.buf p.toNat n.toNat)) ∧
    (SC.step (SC.seek t p 0).1 (.read (some n))).2 = .ok (.str (slice t.buf p.toNat n.toNat))) ∧
  (P.read (P.seek s p 0).1 (some n)).2 = .ok (.bytes (slice s.buf p.toNat n.toNat))

theorem slice_readCount (buf : List Nat) (p : Nat) (n : Int) (hn : 0 ≤ n) :
    slice buf p (readCount buf.length p n) = slice buf p n.toNat := by
  unfold readCount slice
  split
  · next h => rw [List.drop_eq_nil_of_le h]; simp
  · have : ¬ n < 0 := by omega
    simp only [this, ite_false]
    by_cases hm : n.toNat ≤ buf.length - p
    · rw [Nat.min_eq_left hm]
    · rw [Nat.min_eq_right (by omega), List.take_of_length_le (by simp),
        List.take_of_length_le (by simp; omega)]

theorem readAfterSeek_proven : ReadAfterSeek := by
  intro s t p n hc htc hp hn
  obtain ⟨buf, pos, cl, ex, sh⟩ := s
  simp only at hc; subst hc
  constructor
  · intro hP hN
    have h0 : InCInt 0 := by decide
    have hneg : ¬ p < 0 := by omega
    constructor
    · have hs : C.seek ⟨buf, pos, false, ex, sh⟩ p 0 = (⟨buf, p.toNat, false, ex, sh⟩, .ok (.int p)) := by
        simp [C.seek, argSsize, argCInt, hP, h0, hneg]
      rw [hs, C_read_open _ _ rfl (by intro v hv; cases hv; exact hN)]
      simp [slice_readCount _ _ _ hn]
    · have hs : (SC.seek t p 0).1 = { t with pos := p.toNat } := by
        simp [SC.seek, argSsize, argCInt, hP, h0, htc, hneg]
      have hcnt := cnt_eq t.buf.length p.toNat n
      rw [hs]
      simp only [SC.step, optSsize, hN, ite_true, htc, Bool.false_eq_true, ite_false]
      rw [hcnt, slice_readCount _ _ _ hn]
  · have : ¬ p < 0 := by omega
    have hs : P.seek ⟨buf, pos, false, ex, sh⟩ p 0 = (⟨buf, p.toNat, false, ex, sh⟩, .ok (.int p)) := by
      simp [P.seek, this]
    rw [hs]
    simp only [P.read]
    rw [P_read_open _ _ rfl]
    simp [slice_readCount _ _ _ hn, Except.map]

/-- `truncate()` never moves the stream position, whatever its argument and
outcome (both BytesIO twins and the C StringIO). -/
def TruncateKeepsPosition : Prop := ∀ (s : BState) (t : SCState) (n : Option Int),
  (C.truncate s n).1.pos = s.pos ∧ (P.truncate s n).1.pos = s.pos ∧ (SC.step t (.truncate n)).1.pos = t.pos

theorem truncateKeepsPosition_proven : TruncateKeepsPosition := by
  intro s t n
  refine ⟨?_, ?_, ?_⟩
  · unfold C.truncate; dsimp only
    repeat' (first | rfl | split)
  · unfold P.truncate; dsimp only
    repeat' (first | rfl | split)
  · simp only [SC.step]
    repeat' (first | rfl | split)

/-- After a successful `write(b)` of a non-empty `b` on an open stream,
`getvalue()` returns the old contents overwritten by `b` at the old
position, with any gap between the old end and that position filled with
zero bytes (both BytesIO twins); an empty write changes nothing. -/
def GetvalueZeroFill : Prop := ∀ (s : BState) (b : List Nat), s.closed = false →
  ((C.write s b).2.isOk = true →
    (C.step (C.write s b).1 .getvalue).2 = .ok (.bytes (if b = [] then s.buf else writeAt s.buf s.pos b)) ∧
    ZeroFill s.buf s.pos b (writeAt s.buf s.pos b)) ∧
  ((P.write s b).2.isOk = true →
    (P.step (P.write s b).1 .getvalue).2 = .ok (.bytes (if b = [] then s.buf else writeAt s.buf s.pos b)) ∧
    ZeroFill s.buf s.pos b (writeAt s.buf s.pos b))

theorem getvalueZeroFill_proven : GetvalueZeroFill := by
  intro s b hc
  constructor
  · intro h
    refine ⟨?_, writeAt_zeroFill _ _ _⟩
    cases hw : (C.write s b).2 with
    | error e => rw [hw] at h; simp [Except.isOk, Except.toBool] at h
    | ok v =>
      obtain ⟨-, hs⟩ := C_write_ok s b v hw
      rw [hs]
      split
      · simp [C.step, hc]
      · simp [C.step, hc]
  · intro h
    refine ⟨?_, writeAt_zeroFill _ _ _⟩
    cases hw : (P.write s b).2 with
    | error e => rw [hw] at h; simp [Except.isOk, Except.toBool] at h
    | ok v =>
      obtain ⟨-, hs⟩ := P_write_ok s b v hw
      rw [hs]
      split
      · simp [P.step, hc]
      · simp [P.step, hc]

/-- Writing `ws` one after another into a fresh `BytesIO()` leaves exactly
their concatenation in `getvalue()` (both twins), while the total stays
below the allocation bound. -/
def WritesConcat : Prop := ∀ ws : List (List Nat), (ws.map List.length).sum < memLimit →
  (runBC [] (ws.map .write ++ [.getvalue])).getLast? = some (.ok (.bytes ws.flatten)) ∧
  (runBPy [] (ws.map .write ++ [.getvalue])).getLast? = some (.ok (.bytes ws.flatten))

theorem writeAt_end (buf b : List Nat) : writeAt buf buf.length b = buf ++ b := by
  unfold writeAt
  simp [List.drop_eq_nil_of_le]

theorem runOps_append {σ ω : Type} (step : σ → ω → σ × Py Val) (s : σ) (xs ys : List ω) :
    (runOps step s (xs ++ ys)).2 = (runOps step s xs).2 ++ (runOps step (runOps step s xs).1 ys).2 := by
  induction xs generalizing s with
  | nil => simp [runOps]
  | cons x xs ih => simp [runOps, ih]

theorem C_writes (pre : List Nat) (sh : Bool) : ∀ ws : List (List Nat),
    pre.length + (ws.map List.length).sum < memLimit →
    (runOps C.step ⟨pre, pre.length, false, 0, sh⟩ (ws.map .write)).1.buf = pre ++ ws.flatten ∧
    (runOps C.step ⟨pre, pre.length, false, 0, sh⟩ (ws.map .write)).1.pos = (pre ++ ws.flatten).length ∧
    (runOps C.step ⟨pre, pre.length, false, 0, sh⟩ (ws.map .write)).1.closed = false ∧
    (runOps C.step ⟨pre, pre.length, false, 0, sh⟩ (ws.map .write)).1.exports = 0 := by
  intro ws
  induction ws generalizing pre sh with
  | nil => intro _; simp [runOps]
  | cons w ws ih =>
    intro hlen
    simp only [List.map_cons, List.sum_cons] at hlen
    have hmax : memLimit ≤ ssizeMax := by decide
    simp only [List.map_cons, runOps, C.step, C.write, Bool.false_eq_true, ite_false, Nat.lt_irrefl]
    by_cases hw : w.length = 0
    · have : w = [] := List.eq_nil_of_length_eq_zero hw
      subst this
      have := ih pre sh (by simpa using hlen)
      simpa using this
    · have c1 : ¬ (pre.length + w.length > pre.length ∧ ((pre.length + w.length : Nat) : Int) > ssizeMax) := by
        omega
      have c2 : ¬ (pre.length + w.length > pre.length ∧ ((pre.length + w.length : Nat) : Int) = ssizeMax) := by
        omega
      have c3 : ¬ (pre.length + w.length > pre.length ∧ pre.length + w.length ≥ memLimit) := by omega
      simp only [hw, c1, c2, c3, ite_false]
      have := ih (pre ++ w) false (by simp; omega)
      simp only [List.length_append, writeAt_end] at this ⊢
      simpa [List.append_assoc, Nat.add_assoc] using this

theorem P_writes (pre : List Nat) (sh : Bool) : ∀ ws : List (List Nat),
    pre.length + (ws.map List.length).sum < memLimit →
    (runOps P.step ⟨pre, pre.length, false, 0, sh⟩ (ws.map .write)).1.buf = pre ++ ws.flatten ∧
    (runOps P.step ⟨pre, pre.length, false, 0, sh⟩ (ws.map .write)).1.closed = false := by
  intro ws
  induction ws generalizing pre with
  | nil => intro _; simp [runOps]
  | cons w ws ih =>
    intro hlen
    simp only [List.map_cons, List.sum_cons] at hlen
    simp only [List.map_cons, runOps, P.step, P.write, Bool.false_eq_true, ite_false, Nat.lt_irrefl]
    by_cases hw : w.length = 0
    · have : w = [] := List.eq_nil_of_length_eq_zero hw
      subst this
      have := ih pre (by simpa using hlen)
      simpa using this
    · have c3 : ¬ (pre.length + w.length ≥ memLimit) := by omega
      simp only [hw, c3, ite_false, Nat.lt_irrefl, false_and]
      have := ih (pre ++ w) (by simp; omega)
      simp only [List.length_append, writeAt_end] at this ⊢
      simpa [List.append_assoc] using this

theorem writesConcat_proven : WritesConcat := by
  intro ws hlen
  constructor
  · unfold runBC
    rw [runOps_append]
    have := C_writes [] true ws (by simpa using hlen)
    simp only [bInit, List.length_nil, List.nil_append] at this ⊢
    obtain ⟨h1, -, h3, -⟩ := this
    simp [runOps, C.step, h1, h3, List.getLast?_append]
  · unfold runBPy
    rw [runOps_append]
    have := P_writes [] true ws (by simpa using hlen)
    simp only [bInit, List.length_nil, List.nil_append] at this ⊢
    obtain ⟨h1, h3⟩ := this
    simp [runOps, P.step, h1, h3, List.getLast?_append]

end PyLean.PyIO
