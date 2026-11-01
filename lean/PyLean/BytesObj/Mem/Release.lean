import PyLean.BytesObj.Mem.Pack

/-!
The release rules: export counting, idempotence, what a released view refuses, the
getters, and the two places where a release in a Python callback goes unnoticed.
-/

namespace PyLean.BytesObj.Mem

open PyLean

/-! ## Monotonicity of release -/

/-- `st'` is `st` with possibly more objects released. -/
structure Mono (st st' : St) : Prop where
  mv : ∀ j, (st.mv j).flags.released = true → (st'.mv j).flags.released = true
  mbuf : ∀ j, (st'.mv j).mbuf = (st.mv j).mbuf
  mb : ∀ k, (st.mb k).released = true → (st'.mb k).released = true
  mem : st'.mem = st.mem
  iters : st'.iters = st.iters
  view : ∀ j, (st'.mv j).view = (st.mv j).view

theorem Mono.refl (st : St) : Mono st st := ⟨fun _ h => h, fun _ => rfl, fun _ h => h, rfl, rfl, fun _ => rfl⟩

theorem Mono.trans {a b c : St} (h1 : Mono a b) (h2 : Mono b c) : Mono a c :=
  ⟨fun j h => h2.mv j (h1.mv j h), fun j => by rw [h2.mbuf, h1.mbuf],
   fun k h => h2.mb k (h1.mb k h), by rw [h2.mem, h1.mem], by rw [h2.iters, h1.iters],
   fun j => by rw [h2.view, h1.view]⟩

theorem Mono.inaccessible {st st' : St} (h : Mono st st') (i : Nat)
    (hi : baseInaccessible st i = true) : baseInaccessible st' i = true := by
  unfold baseInaccessible at *
  rw [h.mbuf]
  simp only [Bool.or_eq_true] at *
  rcases hi with hi | hi
  · exact Or.inl (h.mv _ hi)
  · exact Or.inr (h.mb _ hi)

theorem mv_getD_set (l : List MV) (i j : Nat) (x : MV) :
    (l.set i x).getD j default = if i = j ∧ i < l.length then x else l.getD j default := by
  by_cases h : i = j
  · subst h
    by_cases hl : i < l.length
    · simp [List.getD_eq_getElem?_getD, hl]
    · simp [List.getD_eq_getElem?_getD, hl]
  · simp [List.getD_eq_getElem?_getD, h]

theorem mb_getD_set (l : List MBuf) (i j : Nat) (x : MBuf) :
    (l.set i x).getD j default = if i = j ∧ i < l.length then x else l.getD j default := by
  by_cases h : i = j
  · subst h
    by_cases hl : i < l.length
    · simp [List.getD_eq_getElem?_getD, hl]
    · simp [List.getD_eq_getElem?_getD, hl]
  · simp [List.getD_eq_getElem?_getD, h]

theorem Mono.setMv (st : St) (i : Nat) (x : MV) (h1 : (st.mv i).flags.released = true → x.flags.released = true)
    (h2 : x.mbuf = (st.mv i).mbuf)
    (h3 : x.view = (st.mv i).view) : Mono st (st.setMv i x) := by
  refine ⟨?_, ?_, fun _ h => h, rfl, rfl, ?_⟩
  · intro j hj
    simp only [St.mv, St.setMv, mv_getD_set] at *
    split
    · rename_i hc; rw [← hc.1] at hj; exact h1 hj
    · exact hj
  · intro j
    simp only [St.mv, St.setMv, mv_getD_set] at *
    split
    · rename_i hc; rw [h2, hc.1]
    · rfl
  · intro j
    simp only [St.mv, St.setMv, mv_getD_set]
    split
    · rename_i hc; rw [h3, hc.1]; rfl
    · rfl

theorem Mono.setMb (st : St) (k : Nat) (x : MBuf) (h1 : (st.mb k).released = true → x.released = true) :
    Mono st (st.setMb k x) := by
  refine ⟨fun _ h => h, fun _ => rfl, ?_, rfl, rfl, fun _ => rfl⟩
  intro j hj
  simp only [St.mb, St.setMb, mb_getD_set] at *
  split
  · rename_i hc; rw [← hc.1] at hj; exact h1 hj
  · exact hj

theorem pyBufferRelease0_mono (b : Buf) (st : St) : Mono st (pyBufferRelease0 b st).2 := by
  unfold pyBufferRelease0
  split
  · exact Mono.setMv _ _ _ id rfl rfl
  · exact Mono.refl _

theorem hookRelease_mono (rel : Nat → M Unit) (hr : ∀ t s, Mono s (rel t s).2) (b : Buf) (st : St) :
    Mono st (hookRelease rel b st).2 := by
  unfold hookRelease
  split
  · dsimp only
    split
    · exact (hr _ _).trans (pyBufferRelease0_mono _ _)
    · exact pyBufferRelease0_mono _ _
  · exact pyBufferRelease0_mono _ _

theorem mbufReleaseWith_mono (rel : Nat → M Unit) (hr : ∀ t s, Mono s (rel t s).2) (k : Nat) (st : St) :
    Mono st (mbufReleaseWith rel k st).2 := by
  unfold mbufReleaseWith
  dsimp only
  split
  · exact Mono.refl _
  · exact (Mono.setMb _ _ _ (fun _ => rfl)).trans (hookRelease_mono rel hr _ _)

theorem memoryReleaseAt_mono : ∀ (f i : Nat) (st : St), Mono st (memoryReleaseAt f i st).2
  | 0, _, _ => Mono.refl _
  | f + 1, i, st => by
    unfold memoryReleaseAt
    dsimp only
    split
    · exact Mono.refl _
    · have h1 := Mono.setMv st i { st.mv i with flags := { (st.mv i).flags with released := true } }
        (fun _ => rfl) rfl rfl
      have h2 := Mono.setMb (st.setMv i { st.mv i with flags := { (st.mv i).flags with released := true } })
        (st.mv i).mbuf
        { (st.setMv i { st.mv i with flags := { (st.mv i).flags with released := true } }).mb (st.mv i).mbuf with
          exports := ((st.setMv i { st.mv i with flags := { (st.mv i).flags with released := true } }).mb
            (st.mv i).mbuf).exports - 1 } id
      have h3 := h1.trans h2
      split
      · exact h3.trans (mbufReleaseWith_mono _ (fun t s => memoryReleaseAt_mono f t s) _ _)
      · exact h3

theorem memoryRelease0_mono (i : Nat) (st : St) : Mono st (memoryRelease0 i st).2 :=
  memoryReleaseAt_mono _ _ _

theorem pyBufferRelease_mono (b : Buf) (st : St) : Mono st (pyBufferRelease b st).2 := by
  unfold pyBufferRelease
  split
  · dsimp only
    split
    · exact (memoryRelease0_mono _ _).trans (pyBufferRelease0_mono _ _)
    · exact pyBufferRelease0_mono _ _
  · exact pyBufferRelease0_mono _ _

theorem mbufRelease_mono (k : Nat) (st : St) : Mono st (mbufRelease k st).2 := by
  unfold mbufRelease
  dsimp only
  split
  · exact Mono.refl _
  · exact (Mono.setMb _ _ _ (fun _ => rfl)).trans (pyBufferRelease_mono _ _)

theorem memoryRelease_mono (i : Nat) (st : St) : Mono st (memoryRelease i st).2 := by
  unfold memoryRelease
  dsimp only
  split
  · exact Mono.refl _
  · have h1 := Mono.setMv st i { st.mv i with flags := { (st.mv i).flags with released := true } }
      (fun _ => rfl) rfl rfl
    have h2 := Mono.setMb (st.setMv i { st.mv i with flags := { (st.mv i).flags with released := true } })
      (st.mv i).mbuf
      { (st.setMv i { st.mv i with flags := { (st.mv i).flags with released := true } }).mb (st.mv i).mbuf with
        exports := ((st.setMv i { st.mv i with flags := { (st.mv i).flags with released := true } }).mb
          (st.mv i).mbuf).exports - 1 } id
    have h3 := h1.trans h2
    split
    · exact h3.trans (mbufRelease_mono _ _)
    · exact h3

theorem fire_mono (r : Option Nat) (st : St) : Mono st (fire r st).2 := by
  cases r with
  | none => exact Mono.refl _
  | some i =>
    show Mono st (if getExports st i = 0 then memoryRelease i st else (.ok (), st)).2
    split
    · exact memoryRelease_mono _ _
    · exact Mono.refl _

/-! ## Export counting -/

/-- `m.release()` (Doc/library/stdtypes.rst, `release`; memoryobject.c:1104-1148), for every state.
With exported buffers it raises `BufferError("memoryview has N exported buffer(s)")` and changes
nothing; a negative count is `SystemError`. With none it marks the view released, whatever a
`__release_buffer__` then does, and a released view is left alone. The managed buffer loses one view:
while others remain nothing else happens, and when the last one goes it is released, which runs the
exporter's hook. What the hook does is `ReentrantRelease`. Hypotheses: `i` and its managed buffer are
live objects. -/
def ReleaseRules : Prop :=
  ∀ (st : St) (i : Nat), i < st.mvs.length → (st.mv i).mbuf < st.mbufs.length →
    let k := (st.mv i).mbuf
    let r := memoryviewRelease i st
    ((st.mv i).exports > 0 →
      r.1 = .error (bufferError s!"memoryview has {(st.mv i).exports} exported buffer{if (st.mv i).exports = 1 then "" else "s"}") ∧
      r.2 = st ∧ memoryExit i st = r) ∧
    ((st.mv i).exports < 0 → r.1 = .error (systemError "memoryview: negative export count") ∧ r.2 = st) ∧
    ((st.mv i).exports = 0 → r.1 = .ok () ∧ baseInaccessible r.2 i = true ∧
      ((r.2.mv i).exports = 0 → memoryviewRelease i r.2 = (.ok (), r.2)) ∧
      ((st.mv i).flags.released = true → r.2 = st) ∧
      ((st.mv i).flags.released = false →
        ((st.mb k).exports ≠ 1 → (r.2.mb k).exports = (st.mb k).exports - 1 ∧
          (r.2.mb k).released = (st.mb k).released) ∧
        ((st.mb k).exports = 1 → (r.2.mb k).released = true)))

theorem exports_setMv_self (st : St) (i : Nat) (x : MV) (hi : i < st.mvs.length) :
    (st.setMv i x).mv i = x := St.mv_setMv st i x hi

theorem second_release (s : St) (i : Nat) (h1 : (s.mv i).flags.released = true)
    (h2 : (s.mv i).exports = 0) :
    memoryviewRelease i s = (.ok (), s) ∧ baseInaccessible s i = true := by
  constructor
  · simp [memoryviewRelease, getExports, h2, memoryRelease, h1]
  · simp [baseInaccessible, h1]

theorem mbufRelease_res (k : Nat) (st : St) : (mbufRelease k st).1 = .ok () := by
  unfold mbufRelease
  dsimp only
  split
  · rfl
  · exact pyBufferRelease_ok _ _

theorem mbufRelease_marks (k : Nat) (st : St) (hk : k < st.mbufs.length) :
    ((mbufRelease k st).2.mb k).released = true := by
  unfold mbufRelease
  dsimp only
  split
  · assumption
  · refine (pyBufferRelease_mono _ _).mb k ?_
    rw [St.mb_setMb _ _ _ hk]

theorem releaseRules_proven : ReleaseRules := by
  intro st i hi hk
  dsimp only
  generalize hx : st.mv i = x at *
  have hmr : ∀ h0 : x.exports = 0, memoryviewRelease i st = memoryRelease i st := by
    intro h0
    unfold memoryviewRelease getExports
    simp [hx, h0]
  refine ⟨fun hpos => ?_, fun hneg => ?_, fun h0 => ?_⟩
  · have h1 : ¬ x.exports = 0 := by omega
    have : memoryviewRelease i st = (.error (bufferError s!"memoryview has {x.exports} exported buffer{if x.exports = 1 then "" else "s"}"), st) := by
      unfold memoryviewRelease getExports
      simp [hx, h1, hpos]
    rw [this]
    exact ⟨rfl, rfl, by rw [← this]; rfl⟩
  · have h1 : ¬ x.exports = 0 := by omega
    have h2 : ¬ x.exports > 0 := by omega
    have : memoryviewRelease i st = (.error (systemError "memoryview: negative export count"), st) := by
      unfold memoryviewRelease getExports
      simp [hx, h1, h2]
    rw [this]
    exact ⟨rfl, rfl⟩
  · rw [hmr h0]
    by_cases hrel : x.flags.released = true
    · have e : memoryRelease i st = (.ok (), st) := by simp [memoryRelease, hx, hrel]
      rw [e]
      have := second_release st i (by rw [hx]; exact hrel) (by rw [hx]; exact h0)
      exact ⟨rfl, this.2, fun _ => this.1, fun _ => rfl, fun h => by rw [hrel] at h; cases h⟩
    · have hf : x.flags.released = false := by simpa using hrel
      generalize hy : ({ x with flags := { x.flags with released := true } } : MV) = y
      generalize hst1 : st.setMv i y = st1
      have hb : st1.mb x.mbuf = st.mb x.mbuf := by rw [← hst1]; rfl
      generalize hbb : st.mb x.mbuf = b at *
      generalize hst2 : st1.setMb x.mbuf { b with exports := b.exports - 1 } = st2
      have hk1 : x.mbuf < st1.mbufs.length := by rw [← hst1]; exact hk
      have hk2 : x.mbuf < st2.mbufs.length := by rw [← hst2]; simpa [St.setMb] using hk1
      have hmv1 : st1.mv i = y := by rw [← hst1]; exact St.mv_setMv _ _ _ hi
      have hmv2 : st2.mv i = y := by rw [← hst2, St.mv_setMb]; exact hmv1
      have hmb2 : st2.mb x.mbuf = { b with exports := b.exports - 1 } := by
        rw [← hst2]; exact St.mb_setMb _ _ _ hk1
      have hyrel : y.flags.released = true := by rw [← hy]
      have hm : memoryRelease i st =
          (if b.exports - 1 = 0 then mbufRelease x.mbuf st2 else (.ok (), st2)) := by
        simp only [memoryRelease, hx, hf, Bool.false_eq_true, ↓reduceIte, hy, hst1, hb]
        simp only [hst2]
      rw [hm]
      by_cases he : b.exports - 1 = 0
      · rw [if_pos he]
        have hmono := mbufRelease_mono x.mbuf st2
        have hmv3 : ((mbufRelease x.mbuf st2).2.mv i).flags.released = true :=
          hmono.mv i (by rw [hmv2]; exact hyrel)
        refine ⟨mbufRelease_res x.mbuf st2, ?_, fun h3 => (second_release _ i hmv3 h3).1,
          (fun h => by rw [hf] at h; cases h), fun _ => ⟨fun h => by omega, fun _ => ?_⟩⟩
        · simp [baseInaccessible, hmv3]
        · exact mbufRelease_marks _ _ hk2
      · rw [if_neg he]
        have := second_release st2 i (by rw [hmv2]; exact hyrel) (by
          rw [hmv2, ← hy]; exact h0)
        refine ⟨rfl, this.2, fun _ => this.1, (fun h => by rw [hf] at h; cases h),
          fun _ => ⟨fun _ => ?_, fun h => by omega⟩⟩
        rw [hmb2]
        exact ⟨rfl, rfl⟩

/-- `__release_buffer__` in the states a release can reach, when view `i` is the last of its buffer.
The view being released, or any view released already, which is every other view of this buffer: the
`m.release()` in the hook does nothing. The view this release gives an export back to: it still holds
that export, so `m.release()` raises `BufferError`, which the hook swallows, and the export then goes
back with the view unreleased. Hypotheses: live objects, and the cases named. -/
def ReentrantRelease : Prop :=
  ∀ (st : St) (i t : Nat), i < st.mvs.length → (st.mv i).mbuf < st.mbufs.length →
    (st.mv i).flags.released = false →
    let k := (st.mv i).mbuf
    let b := st.mb k
    b.exports = 1 → b.released = false → b.master.hook = some t →
    let s1 := st.setMv i { st.mv i with flags := { (st.mv i).flags with released := true } }
    let s3 := (s1.setMb k { b with exports := 0 }).setMb k { b with exports := 0, released := true }
    ((t = i ∨ (st.mv t).flags.released = true) → memoryRelease i st = pyBufferRelease0 b.master s3) ∧
    (t ≠ i → (st.mv t).exports > 0 → memoryRelease i st = pyBufferRelease0 b.master s3 ∧
      (b.master.obj = some (.mv t) → t < st.mvs.length →
        ((memoryRelease i st).2.mv t).exports = (st.mv t).exports - 1 ∧
        ((memoryRelease i st).2.mv t).flags = (st.mv t).flags))

theorem memoryReleaseAt_done (f t : Nat) (s : St) (h : (s.mv t).flags.released = true) :
    memoryReleaseAt f t s = (.ok (), s) := by
  cases f with
  | zero => rfl
  | succ f => simp [memoryReleaseAt, h]

theorem reentrantRelease_proven : ReentrantRelease := by
  intro st i t hi hk hrel
  dsimp only
  intro he hr hh
  generalize hb : st.mb (st.mv i).mbuf = b at *
  generalize hy : ({ st.mv i with flags := { (st.mv i).flags with released := true } } : MV) = y
  generalize hs1 : st.setMv i y = s1
  have hbm : s1.mb (st.mv i).mbuf = b := by rw [← hs1]; exact hb
  have hk1 : (st.mv i).mbuf < s1.mbufs.length := by rw [← hs1]; exact hk
  generalize hs2 : s1.setMb (st.mv i).mbuf { b with exports := 0 } = s2
  have hk2 : (st.mv i).mbuf < s2.mbufs.length := by rw [← hs2]; simpa [St.setMb] using hk1
  have hmb2 : s2.mb (st.mv i).mbuf = { b with exports := 0 } := by rw [← hs2]; exact St.mb_setMb _ _ _ hk1
  generalize hs3 : s2.setMb (st.mv i).mbuf { b with exports := 0, released := true } = s3
  have hmv3 : ∀ j, s3.mv j = s1.mv j := fun j => by rw [← hs3, St.mv_setMb, ← hs2, St.mv_setMb]
  have hstep : memoryRelease i st = pyBufferRelease b.master s3 := by
    have e0 : b.exports - 1 = 0 := by omega
    have h1 : memoryRelease i st =
        (if b.exports - 1 = 0 then mbufRelease (st.mv i).mbuf (s1.setMb (st.mv i).mbuf { b with exports := b.exports - 1 })
         else (.ok (), s1.setMb (st.mv i).mbuf { b with exports := b.exports - 1 })) := by
      simp only [memoryRelease, hrel, Bool.false_eq_true, ↓reduceIte, hy, hs1, hbm]
    rw [h1, if_pos e0, e0, hs2]
    have h2 : mbufRelease (st.mv i).mbuf s2 =
        pyBufferRelease (s2.mb (st.mv i).mbuf).master
          (s2.setMb (st.mv i).mbuf { s2.mb (st.mv i).mbuf with released := true }) := by
      unfold mbufRelease
      dsimp only
      rw [if_neg (by rw [hmb2]; simpa using hr)]
    rw [h2, hmb2, ← hs3]
  have hzero : ∀ s (hs : (s.mv t).flags.released = true), memoryRelease0 t s = (.ok (), s) :=
    fun s hs => memoryReleaseAt_done _ _ _ hs
  have hst : ∀ j, j ≠ i → s3.mv j = st.mv j := by
    intro j hj
    rw [hmv3, ← hs1]
    exact St.mv_setMv_ne _ _ _ _ (Ne.symm hj)
  constructor
  · intro hc
    have hs : (s3.mv t).flags.released = true := by
      rw [hmv3, ← hs1]
      rcases hc with rfl | hc
      · rw [St.mv_setMv _ _ _ hi, ← hy]
      · by_cases hti : t = i
        · subst hti
          rw [St.mv_setMv _ _ _ hi, ← hy]
        · rw [St.mv_setMv_ne _ _ _ _ (Ne.symm hti)]
          exact hc
    rw [hstep]
    simp only [pyBufferRelease, hh, hzero _ hs, ite_self]
  · intro hne hpos
    have hx : ¬ (s3.mv t).exports = 0 := by
      rw [hst t hne]
      omega
    have e : memoryRelease i st = pyBufferRelease0 b.master s3 := by
      rw [hstep]
      simp only [pyBufferRelease, hh, hx, ↓reduceIte]
    refine ⟨e, fun hobj ht => ?_⟩
    rw [e]
    simp only [pyBufferRelease0, hobj]
    have hlen : t < s3.mvs.length := by
      rw [← hs3, ← hs2, ← hs1]
      simpa [St.setMb, St.setMv] using ht
    rw [St.mv_setMv _ _ _ hlen, hst t hne]
    exact ⟨rfl, rfl⟩

/-- What a released view refuses: once `BASE_INACCESSIBLE` holds, every operation of the
object raises `ValueError("operation forbidden on released memoryview object")` before
touching the buffer. Quantified over every state in which the base is inaccessible, every
argument. Doc/library/stdtypes.rst, `release`: "After this method has been called, any
further operation on the view raises a ValueError". -/
def ReleasedForbids : Prop :=
  ∀ (st : St) (i : Nat), baseInaccessible st i = true →
    (∀ a, (memoryGet i a st).1 = .error releasedError) ∧
    (memoryviewTolist i st).1 = .error releasedError ∧
    (∀ o, (memoryviewTobytes i o st).1 = .error releasedError) ∧
    (∀ s n, (memoryviewHex i s n st).1 = .error releasedError) ∧
    (∀ f s, (memoryviewCast i f s st).1 = .error releasedError) ∧
    (memoryviewToreadonly i st).1 = .error releasedError ∧
    (∀ k, (memorySubscript i k st).1 = .error releasedError) ∧
    (∀ k v, (memoryAssSub i k v st).1 = .error releasedError) ∧
    (memoryLength i st).1 = .error releasedError ∧
    (memoryIter i st).1 = .error releasedError ∧
    (∀ v, (memoryviewCount i v st).1 = .error releasedError) ∧
    (∀ v a b, (memoryviewIndex i v a b st).1 = .error releasedError) ∧
    (memoryEnter i st).1 = .error releasedError ∧
    (∀ f, (memoryGetbuf i f st).1 = .error releasedError) ∧
    (∀ f, (memoryViewFromObjectAndFlags (.view i) f st).1 = .error releasedError)

theorem releasedForbids_proven : ReleasedForbids := by
  intro st i h
  have e := checkReleased_err st i h
  have b : ∀ {α : Type} (f : Unit → M α), (checkReleased i >>= f) st = (.error releasedError, st) :=
    fun f => bind_err _ f st st _ e
  refine ⟨fun a => ?_, ?_, fun o => ?_, fun s n => ?_, fun f s => ?_, ?_, fun k => ?_, fun k v => ?_,
    ?_, ?_, fun v => ?_, fun v a c => ?_, ?_, fun f => ?_, fun f => ?_⟩
  all_goals first
    | (simp only [memoryGet, b]; done)
    | (simp only [memoryviewTolist, b]; done)
    | (simp only [memoryviewTobytes, b]; done)
    | (simp only [memoryviewHex, b]; done)
    | (simp only [memoryviewCast, b]; done)
    | (simp only [memoryviewToreadonly, b]; done)
    | (simp only [memorySubscript, b]; done)
    | (simp only [memoryAssSub, b]; done)
    | (simp only [memoryLength, b]; done)
    | (simp only [memoryIter, b]; done)
    | (simp only [memoryviewIndex, b]; done)
    | (simp only [memoryEnter, b]; done)
    | (simp only [memoryGetbuf, b]; done)
    | (simp only [memoryViewFromObjectAndFlags, b]; done)
    | (simp only [memoryviewCount, memoryIter, M.bind_app, e]; done)

/-- The getters report the buffer: for a live view each attribute is the field it names,
with an empty tuple for a NULL array and the three contiguity bits read from the flags
(Doc/library/stdtypes.rst, `memoryview` attributes). -/
def GettersReport : Prop :=
  ∀ (st : St) (i : Nat), baseInaccessible st i = false →
    let v := (st.mv i).view
    let f := (st.mv i).flags
    memoryGet i .obj st = (.ok (.obj v.obj), st) ∧
    memoryGet i .nbytes st = (.ok (.int v.len), st) ∧
    memoryGet i .readonly st = (.ok (.bool v.readonly), st) ∧
    memoryGet i .itemsize st = (.ok (.int v.itemsize), st) ∧
    memoryGet i .format st = (.ok (.fmt (v.format.getD [])), st) ∧
    memoryGet i .ndim st = (.ok (.int v.ndim), st) ∧
    memoryGet i .shape st = (.ok (.tuple ((v.shape.getD []).take v.ndim)), st) ∧
    memoryGet i .strides st = (.ok (.tuple ((v.strides.getD []).take v.ndim)), st) ∧
    memoryGet i .suboffsets st = (.ok (.tuple ((v.suboffsets.getD []).take v.ndim)), st) ∧
    memoryGet i .cContiguous st = (.ok (.bool (f.scalar || f.c)), st) ∧
    memoryGet i .fContiguous st = (.ok (.bool (f.scalar || f.fortran)), st) ∧
    memoryGet i .contiguous st = (.ok (.bool (f.scalar || f.c || f.fortran)), st)

theorem gettersReport_proven : GettersReport := by
  intro st i h
  have e := checkReleased_ok st i h
  have tup : ∀ (n : Nat) (o : Option (List Int)),
      intTupleFromSsizet n o = (o.getD []).take n := by
    intro n o; cases o <;> simp [intTupleFromSsizet]
  simp only [memoryGet, M.bind_app, e, M.get, M.pure_app, tup, Flags.isC, Flags.isF, Flags.isAny]
  simp

end PyLean.BytesObj.Mem
