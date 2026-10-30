import PyLean.PyIO.BytesCore

/-!
Normal forms of each BytesIO operation on an open stream, for both twins,
and the one-step simulation behind `BytesIOTwinsSameClassCore`.
-/

namespace PyLean.PyIO

open PyLean

/-- Bytes returned by `read(size)` at `pos` in a buffer of length `len`. -/
def readCount (len pos : Nat) (size : Int) : Nat :=
  if len ≤ pos then 0 else if size < 0 then len - pos else min size.toNat (len - pos)

theorem optSsize_ok (d : Int) (n : Option Int) (h : ∀ v, n = some v → InSsize v) :
    optSsize d n = .ok (n.getD d) := by
  cases n with
  | none => rfl
  | some v => simp [optSsize, h v rfl]

theorem cnt_eq (len pos : Nat) (size : Int) :
    (if size < 0 ∨ size > (len : Int) - pos then (if (len : Int) - pos < 0 then 0 else (len : Int) - pos)
      else size).toNat = readCount len pos size := by
  unfold readCount
  by_cases h1 : len ≤ pos
  · simp only [h1, ite_true]; split <;> (try split) <;> omega
  · simp only [h1, ite_false]; split <;> (try split) <;> (try split) <;> omega

theorem pcnt_eq (len pos : Nat) (size : Int) (h : ¬ len ≤ pos) :
    min len (pos + (if size < 0 then (len : Int) else size).toNat) = pos + readCount len pos size := by
  unfold readCount
  simp only [h, ite_false]
  split <;> omega

theorem C_read_open (s : BState) (n : Option Int) (hc : s.closed = false)
    (h : ∀ v, n = some v → InSsize v) :
    C.read s n = ({ s with pos := s.pos + readCount s.buf.length s.pos (n.getD (-1)) },
      .ok (.bytes (slice s.buf s.pos (readCount s.buf.length s.pos (n.getD (-1)))))) := by
  unfold C.read C.readBytes
  rw [optSsize_ok _ _ h]
  simp only [hc, Bool.false_eq_true, ite_false, cnt_eq]

theorem P_read_open (s : BState) (n : Option Int) (hc : s.closed = false) :
    P.readRaw s n = ({ s with pos := s.pos + readCount s.buf.length s.pos (n.getD (-1)) },
      .ok (slice s.buf s.pos (readCount s.buf.length s.pos (n.getD (-1))))) := by
  obtain ⟨buf, pos, cl, ex, sh⟩ := s
  simp only at hc; subst hc
  unfold P.readRaw
  simp only [Bool.false_eq_true, ite_false]
  by_cases h1 : buf.length ≤ pos
  · have : readCount buf.length pos (n.getD (-1)) = 0 := by simp [readCount, h1]
    simp [h1, this, slice]
  · simp only [h1, ite_false, pcnt_eq _ _ _ h1, Nat.add_sub_cancel_left]

theorem scanEol_congr (buf : List Nat) (pos : Nat) (c₁ c₂ : Bool) (e₁ e₂ : Nat) (s₁ s₂ : Bool) (l : Int) :
    C.scanEol ⟨buf, pos, c₁, e₁, s₁⟩ l = C.scanEol ⟨buf, pos, c₂, e₂, s₂⟩ l := rfl

theorem writeAt_pad (buf b : List Nat) (pos : Nat) (h : buf.length < pos) :
    writeAt (buf ++ List.replicate (pos - buf.length) 0) pos b = writeAt buf pos b := by
  have hl : (buf ++ List.replicate (pos - buf.length) 0).length = pos := by simp; omega
  have e1 : (buf ++ List.replicate (pos - buf.length) 0).drop (pos + b.length) = [] :=
    List.drop_eq_nil_of_le (by rw [hl]; omega)
  have e2 : buf.drop (pos + b.length) = [] := List.drop_eq_nil_of_le (by omega)
  unfold writeAt
  rw [e1, e2, hl, Nat.sub_self, List.replicate_zero]
  simp only [List.append_nil]

/-- The C and Python BytesIO states correspond: same buffer, position and
closed flag, and no exported views. -/
def BRel (c p : BState) : Prop :=
  c.buf = p.buf ∧ c.pos = p.pos ∧ c.closed = p.closed ∧ c.exports = 0 ∧ p.exports = 0

theorem bRel_mk (buf : List Nat) (pos : Nat) (cl sh sh' : Bool) :
    BRel ⟨buf, pos, cl, 0, sh⟩ ⟨buf, pos, cl, 0, sh'⟩ := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- One step of the simulation, on a closed stream. -/
theorem step_agree_closed (buf : List Nat) (pos : Nat) (sh sh' : Bool) (o : BOp)
    (hr : o.InRange) (he : o.NoExport) (hz : o.NoReadline0Closed ⟨buf, pos, true, 0, sh'⟩) :
    BRel (C.step ⟨buf, pos, true, 0, sh⟩ o).1 (P.step ⟨buf, pos, true, 0, sh'⟩ o).1 ∧
    sameClass (C.step ⟨buf, pos, true, 0, sh⟩ o).2 (P.step ⟨buf, pos, true, 0, sh'⟩ o).2 = true := by
  have hR := bRel_mk buf pos true sh sh'
  cases o with
  | read n | read1 n =>
    have h : ∀ v, n = some v → InSsize v := by
      intro v hv; subst hv; exact hr
    simp [C.step, C.read, optSsize_ok _ _ h, P.step, P.read, P.readRaw, hR, sameClass, PyExc.className, Except.map,
      C.closedErr]
  | readline n =>
    have h : ∀ v, n = some v → InSsize v := by
      intro v hv; subst hv; exact hr
    have h0 : n.getD (-1) ≠ 0 := by
      cases n with
      | none => simp
      | some v =>
        intro hv; simp at hv; subst hv
        simp [BOp.NoReadline0Closed] at hz
    simp only [C.step, C.readline, optSsize_ok _ _ h, P.step, P.readline, P.readlineRaw, P.readlineLoop]
    have hgo : n.getD (-1) < 0 ∨ 0 < n.getD (-1) := by omega
    simp [hgo, P.readRaw, hR, sameClass, PyExc.className, Except.map, C.closedErr]
  | readlines h =>
    simp [C.step, C.readlines, P.step, P.readlines, hR, sameClass, PyExc.className, Except.map, C.closedErr]
  | readinto n =>
    simp [C.step, C.readinto, P.step, P.readinto, P.readRaw, hR, sameClass, PyExc.className, Except.map, C.closedErr]
  | write b =>
    simp [C.step, C.write, P.step, P.write, hR, sameClass, PyExc.className, Except.map, C.closedErr]
  | seek p w =>
    have h1 : InSsize p := hr.1
    have h2 : InCInt w := hr.2
    simp [C.step, C.seek, argSsize, argCInt, h1, h2, P.step, P.seek, hR, sameClass, PyExc.className, Except.map,
      C.closedErr]
  | tell => simp [C.step, P.step, hR, sameClass, PyExc.className, Except.map, C.closedErr]
  | truncate n => simp [C.step, C.truncate, P.step, P.truncate, hR, sameClass, PyExc.className, Except.map, C.closedErr]
  | getvalue => simp [C.step, P.step, hR, sameClass, PyExc.className, Except.map, C.closedErr]
  | getbuffer => exact absurd he (by simp [BOp.NoExport])
  | release => simp [C.step, P.step, bRelease, BRel, sameClass]
  | close => simp [C.step, P.step, P.close, BRel, sameClass]
  | next =>
    simp [C.step, C.next, P.step, P.next, P.readlineRaw, P.readlineLoop, P.readRaw, hR, sameClass,
      PyExc.className, C.closedErr]
  | closed => simp [C.step, P.step, hR, sameClass]

theorem readinto_open_C (buf : List Nat) (pos ex : Nat) (sh : Bool) (n : Nat) :
    C.readinto ⟨buf, pos, false, ex, sh⟩ n =
      (⟨buf, pos + readCount buf.length pos n, false, ex, sh⟩,
       .ok (.list [.int (readCount buf.length pos n),
         .bytes (slice buf pos (readCount buf.length pos n) ++
           List.replicate (n - readCount buf.length pos n) 255)])) := by
  unfold C.readinto
  simp only [Bool.false_eq_true, ite_false]
  generalize hL : (if (n : Int) > (buf.length : Int) - pos then (buf.length : Int) - pos else (n : Int)) = L
  have hrc : L < 0 → readCount buf.length pos n = 0 := by
    intro h; unfold readCount; split <;> (try split) <;> (try split at hL) <;> omega
  have hrc2 : ¬ L < 0 → L = (readCount buf.length pos n : Int) := by
    intro h; unfold readCount; split <;> (try split) <;> split at hL <;> omega
  by_cases hneg : L < 0
  · simp [hneg, hrc hneg, slice]
  · have e := hrc2 hneg
    have e2 : L.toNat = readCount buf.length pos n := by omega
    simp only [hneg, ite_false, e2]
    rw [e]

theorem readinto_open_P (buf : List Nat) (pos ex : Nat) (sh : Bool) (n : Nat) :
    P.readinto ⟨buf, pos, false, ex, sh⟩ n =
      (⟨buf, pos + readCount buf.length pos n, false, ex, sh⟩,
       .ok (.list [.int (readCount buf.length pos n),
         .bytes (slice buf pos (readCount buf.length pos n) ++
           List.replicate (n - readCount buf.length pos n) 255)])) := by
  unfold P.readinto
  rw [P_read_open _ _ rfl]
  simp only [Option.getD_some]
  have hle : readCount buf.length pos n ≤ (buf.drop pos).length := by
    simp [readCount]; split <;> (try split) <;> omega
  rw [slice_length _ _ _ hle]

/-- One step of the simulation, on an open stream. -/
theorem step_agree_open (buf : List Nat) (pos : Nat) (sh sh' : Bool) (o : BOp)
    (hr : o.InRange) (he : o.NoExport) (hs : o.Small ⟨buf, pos, false, 0, sh'⟩) :
    BRel (C.step ⟨buf, pos, false, 0, sh⟩ o).1 (P.step ⟨buf, pos, false, 0, sh'⟩ o).1 ∧
    sameClass (C.step ⟨buf, pos, false, 0, sh⟩ o).2 (P.step ⟨buf, pos, false, 0, sh'⟩ o).2 = true := by
  cases o with
  | read n | read1 n =>
    have h : ∀ v, n = some v → InSsize v := by
      intro v hv; subst hv; exact hr
    simp only [C.step, P.step, P.read]
    rw [C_read_open _ _ rfl h, P_read_open _ _ rfl]
    simp [BRel, sameClass, Except.map]
  | readline n =>
    have h : ∀ v, n = some v → InSsize v := by
      intro v hv; subst hv; exact hr
    simp only [C.step, C.readline, optSsize_ok _ _ h, P.step, P.readline]
    rw [readlineRaw_eq _ _ rfl]
    simp [C.readBytes, BRel, sameClass, Except.map, scanEol_congr buf pos false false 0 0 sh sh']
  | readlines h =>
    simp only [C.step, C.readlines, P.step, P.readlines, Bool.false_eq_true, ite_false]
    have key : ∀ (hint : Option Int) (m : Int),
        ((hint = none ∧ m ≤ 0) ∨ (hint = some m ∧ m > 0)) →
        BRel (C.readlinesLoop m ⟨buf, pos, false, 0, sh⟩ 0 [] (buf.length + 1)).1
          (P.readlinesLoop hint ⟨buf, pos, false, 0, sh'⟩ 0 [] (buf.length - pos + 2)).1 ∧
        sameClass (C.readlinesLoop m ⟨buf, pos, false, 0, sh⟩ 0 [] (buf.length + 1)).2
          (P.readlinesLoop hint ⟨buf, pos, false, 0, sh'⟩ 0 [] (buf.length - pos + 2)).2 = true := by
      intro hint m hm
      have hP := P_readlinesLoop hint m hm (buf.length - pos + 2) ⟨buf, pos, false, 0, sh'⟩ 0 [] rfl
        (by simp only; omega)
      rw [show ((0 : Nat) : Int) = 0 from rfl] at hP
      rw [C_readlinesLoop, hP]
      rw [rlSpec_fuel buf m (buf.length + 1) (buf.length - pos + 2) pos 0 (by omega) (by omega)]
      simp [BRel, sameClass]
    cases h with
    | none => exact key none (-1) (Or.inl ⟨rfl, by decide⟩)
    | some v =>
      have hv : InSsize v := hr
      simp only [argSsize, hv, ite_true]
      by_cases hv0 : v ≤ 0
      · simp only [hv0, ite_true]; exact key none v (Or.inl ⟨rfl, hv0⟩)
      · simp only [hv0, ite_false]; exact key (some v) v (Or.inr ⟨rfl, by omega⟩)
  | readinto n =>
    simp only [C.step, P.step]
    rw [readinto_open_C, readinto_open_P]
    simp [BRel, sameClass]
  | write b =>
    have hsm : pos + b.length < memLimit := hs
    have hmax : memLimit ≤ ssizeMax := by decide
    simp only [C.step, C.write, P.step, P.write, Bool.false_eq_true, ite_false]
    by_cases hb : b.length = 0
    · simp [hb, BRel, sameClass]
    · simp only [hb, ite_false, Nat.lt_irrefl, false_and]
      have c1 : ¬ ((pos + b.length) > buf.length ∧ ((pos + b.length : Nat) : Int) > ssizeMax) := by omega
      have c2 : ¬ ((pos + b.length) > buf.length ∧ ((pos + b.length : Nat) : Int) = ssizeMax) := by omega
      have c3 : ¬ ((pos + b.length) > buf.length ∧ pos + b.length ≥ memLimit) := by omega
      simp only [c1, c2, c3, ite_false]
      by_cases hp : pos > buf.length
      · have d1 : ¬ ((pos : Int) > ssizeMax) := by omega
        have d2 : ¬ (pos ≥ memLimit) := by omega
        simp only [hp, ite_true, d1, d2, ite_false, Nat.lt_irrefl]
        have d3 : ¬ (pos + b.length ≥ memLimit) := by omega
        simp [d3, writeAt_pad _ _ _ hp, BRel, sameClass]
      · have d3 : ¬ (pos + b.length ≥ memLimit) := by omega
        simp [hp, d3, BRel, sameClass]
  | seek p w =>
    have h1 : InSsize p := hr.1
    have h2 : InCInt w := hr.2
    have hmax : memLimit ≤ ssizeMax := by decide
    obtain ⟨s0, s1, s2⟩ := hs
    simp only at s0 s1 s2
    simp only [C.step, C.seek, argSsize, argCInt, h1, h2, ite_true, P.step, P.seek,
      Bool.false_eq_true, ite_false]
    by_cases hw0 : w = 0
    · subst hw0
      by_cases hp : p < 0
      · simp [hp, sameClass, PyExc.className, BRel]
      · have := s0 rfl
        simp [hp, BRel, sameClass]
    · by_cases hw1 : w = 1
      · subst hw1
        have := s1 rfl
        have c : ¬ (p > ssizeMax - pos) := by omega
        simp only [c, ite_false, show ¬ ((1 : Int) = 0) by decide, and_false]
        by_cases hneg : p + pos < 0
        · have e : max 0 ((pos : Int) + p) = 0 := by omega
          simp [hneg, e, BRel, sameClass]
        · have e : max 0 ((pos : Int) + p) = p + pos := by omega
          simp [hneg, e, BRel, sameClass]
      · by_cases hw2 : w = 2
        · subst hw2
          have := s2 rfl
          have c : ¬ (p > ssizeMax - buf.length) := by omega
          simp only [c, ite_false, show ¬ ((2 : Int) = 0) by decide, show ¬ ((2 : Int) = 1) by decide, and_false]
          by_cases hneg : p + buf.length < 0
          · have e : max 0 ((buf.length : Int) + p) = 0 := by omega
            simp [hneg, e, BRel, sameClass]
          · have e : max 0 ((buf.length : Int) + p) = p + buf.length := by omega
            simp [hneg, e, BRel, sameClass]
        · simp [hw0, hw1, hw2, BRel, sameClass, PyExc.className]
  | tell => simp [C.step, P.step, BRel, sameClass]
  | truncate n =>
    simp only [C.step, C.truncate, P.step, P.truncate, Bool.false_eq_true, ite_false, Nat.lt_irrefl]
    cases n with
    | none =>
      simp only
      have hp0 : ¬ ((pos : Int) < 0) := by omega
      simp only [hp0, ite_false]
      by_cases hl : (pos : Int) < buf.length
      · have : pos < buf.length := by omega
        simp [hl, this, BRel, sameClass]
      · have : ¬ pos < buf.length := by omega
        simp [hl, this, BRel, sameClass]
    | some v =>
      have hv : InSsize v := hr
      simp only [asLong, hv, ite_true]
      by_cases hneg : v < 0
      · simp [hneg, BRel, sameClass, PyExc.className]
      · by_cases hl : v < buf.length
        · simp [hneg, hl, BRel, sameClass]
        · simp [hneg, hl, BRel, sameClass]
  | getvalue => simp [C.step, P.step, BRel, sameClass]
  | getbuffer => exact absurd he (by simp [BOp.NoExport])
  | release => simp [C.step, P.step, bRelease, BRel, sameClass]
  | close => simp [C.step, P.step, P.close, BRel, sameClass]
  | next =>
    simp only [C.step, C.next, P.step, P.next, Bool.false_eq_true, ite_false]
    rw [readlineRaw_eq _ _ rfl]
    simp only [Option.getD_none, scanEol_congr buf pos false false 0 0 sh sh']
    have hle := lineLen_le (buf.drop pos)
    simp only [scanEol_all]
    by_cases hk : lineLen (buf.drop pos) = 0
    · have : slice buf pos (lineLen (buf.drop pos)) = [] := (slice_eq_nil _ _ _ hle).mpr hk
      simp [hk, slice, BRel, sameClass, PyExc.className]
    · have : slice buf pos (lineLen (buf.drop pos)) ≠ [] := fun h => hk ((slice_eq_nil _ _ _ hle).mp h)
      simp [hk, this, C.readBytes, BRel, sameClass]
  | closed => simp [C.step, P.step, BRel, sameClass]

theorem step_agree (c p : BState) (o : BOp) (hR : BRel c p) (hr : o.InRange) (he : o.NoExport)
    (hs : o.Small p) (hz : o.NoReadline0Closed p) :
    BRel (C.step c o).1 (P.step p o).1 ∧ sameClass (C.step c o).2 (P.step p o).2 = true := by
  obtain ⟨buf, pos, cl, ex, sh⟩ := c
  obtain ⟨buf', pos', cl', ex', sh'⟩ := p
  obtain ⟨h1, h2, h3, h4, h5⟩ := hR
  simp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4 h5
  cases cl with
  | true => exact step_agree_closed buf pos sh sh' o hr he hz
  | false => exact step_agree_open buf pos sh sh' o hr he hs

theorem runOps_cons {σ ω : Type} (step : σ → ω → σ × Py Val) (s : σ) (o : ω) (os : List ω) :
    (runOps step s (o :: os)).2 = (step s o).2 :: (runOps step (step s o).1 os).2 := by
  simp [runOps]

theorem run_agree : ∀ (ops : List BOp) (c p : BState), BRel c p →
    (∀ o ∈ ops, BOp.InRange o ∧ BOp.NoExport o) →
    PyRunAll (fun s o => BOp.Small s o ∧ BOp.NoReadline0Closed s o) p ops →
    allSameClass (runOps C.step c ops).2 (runOps P.step p ops).2 = true := by
  intro ops
  induction ops with
  | nil => intros; simp [runOps, allSameClass]
  | cons o os ih =>
    intro c p hR hops hrun
    obtain ⟨⟨hs, hz⟩, hrest⟩ := hrun
    have ho := hops o (List.mem_cons_self ..)
    obtain ⟨hR', hsame⟩ := step_agree c p o hR ho.1 ho.2 hs hz
    rw [runOps_cons, runOps_cons]
    simp only [allSameClass, hsame, Bool.true_and]
    exact ih _ _ hR' (fun o' h => hops o' (List.mem_cons_of_mem _ h)) hrest

/-- With every int argument in C range, no `getbuffer()`, no allocation
failure (positions and write extents of the run below `memLimit`) and no
`readline(0)` on a closed stream, `io.BytesIO` and `_pyio.BytesIO` return
the same values and raise exceptions of the same classes. -/
def BytesIOTwinsSameClassCore : Prop :=
  ∀ init ops, (∀ o ∈ ops, BOp.InRange o ∧ BOp.NoExport o) →
    PyRunAll (fun s o => BOp.Small s o ∧ BOp.NoReadline0Closed s o) (bInit init) ops →
    AllSameClass (runBC init ops) (runBPy init ops)

theorem bytesIOTwinsSameClassCore_proven : BytesIOTwinsSameClassCore := by
  intro init ops hops hrun
  exact run_agree ops (bInit init) (bInit init) ⟨rfl, rfl, rfl, rfl, rfl⟩ hops hrun

end PyLean.PyIO
