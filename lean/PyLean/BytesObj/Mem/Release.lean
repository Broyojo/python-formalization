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

theorem mbufRelease0_mono (k : Nat) (st : St) : Mono st (mbufRelease0 k st).2 := by
  unfold mbufRelease0
  dsimp only
  split
  · exact Mono.refl _
  · exact (Mono.setMb _ _ _ (fun _ => rfl)).trans (pyBufferRelease0_mono _ _)

theorem memoryRelease0_mono (i : Nat) (st : St) : Mono st (memoryRelease0 i st).2 := by
  unfold memoryRelease0
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
    · exact h3.trans (mbufRelease0_mono _ _)
    · exact h3

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

/-- The `__release_buffer__` of view `i`'s managed buffer, if it has one, reaches neither
`i` nor that buffer: its target is released already, or is another view of another
buffer whose master is not `i`. -/
def HookClear (st : St) (i : Nat) : Prop :=
  match (st.mb (st.mv i).mbuf).master.hook with
  | Option.none => True
  | some t =>
    (st.mv t).flags.released = true ∨
      (t ≠ i ∧ (st.mv t).mbuf ≠ (st.mv i).mbuf ∧
        (st.mb (st.mv t).mbuf).master.obj ≠ some (.mv i))

/-- `_memory_release` of a callback's target leaves another view and buffer alone. -/
theorem memoryRelease0_frame (t i k : Nat) (s : St) (h1 : t ≠ i) (h2 : (s.mv t).mbuf ≠ k)
    (h3 : (s.mb (s.mv t).mbuf).master.obj ≠ some (.mv i)) :
    (memoryRelease0 t s).2.mv i = s.mv i ∧ (memoryRelease0 t s).2.mb k = s.mb k := by
  unfold memoryRelease0
  dsimp only
  split
  · exact ⟨rfl, rfl⟩
  · rename_i hf
    generalize hx : s.mv t = x at *
    generalize hs1 : s.setMv t { x with flags := { x.flags with released := true } } = s1
    have hmv1 : s1.mv i = s.mv i := by rw [← hs1]; exact St.mv_setMv_ne _ _ _ _ h1
    have hmb1 : ∀ j, s1.mb j = s.mb j := fun j => by rw [← hs1]; rfl
    generalize hb : s1.mb x.mbuf = b
    generalize hs2 : s1.setMb x.mbuf { b with exports := b.exports - 1 } = s2
    have hmv2 : s2.mv i = s.mv i := by rw [← hs2, St.mv_setMb]; exact hmv1
    have hmb2 : s2.mb k = s.mb k := by
      rw [← hs2, St.mb_setMb_ne _ _ _ _ h2, hmb1]
    split
    · unfold mbufRelease0
      dsimp only
      split
      · exact ⟨hmv2, hmb2⟩
      · generalize hs3 : s2.setMb x.mbuf { s2.mb x.mbuf with released := true } = s3
        have hmv3 : s3.mv i = s.mv i := by rw [← hs3, St.mv_setMb]; exact hmv2
        have hmb3 : s3.mb k = s.mb k := by rw [← hs3, St.mb_setMb_ne _ _ _ _ h2]; exact hmb2
        have hmaster : (s2.mb x.mbuf).master = (s.mb x.mbuf).master := by
          by_cases hl : x.mbuf < s1.mbufs.length
          · rw [← hs2, St.mb_setMb _ _ _ hl, ← hb, hmb1]
          · have : (s1.setMb x.mbuf { b with exports := b.exports - 1 }).mb x.mbuf = s1.mb x.mbuf := by
              simp [St.mb, St.setMb, List.getD_eq_getElem?_getD, List.getElem?_set, hl]
            rw [← hs2, this, hmb1]
        unfold pyBufferRelease0
        split
        · rename_i j hj
          have hne : j ≠ i := by
            rintro rfl
            exact h3 (by rw [← hmaster]; exact hj)
          exact ⟨by simp only; rw [St.mv_setMv_ne _ _ _ _ hne]; exact hmv3,
            by simp only [St.mb_setMv]; exact hmb3⟩
        · exact ⟨hmv3, hmb3⟩
    · exact ⟨hmv2, hmb2⟩

/-- A release's callback leaves the view being released and its buffer as they were. -/
theorem hook_frame (b : Buf) (s : St) (i k : Nat) (hobj : b.obj ≠ some (.mv i))
    (h : match b.hook with
      | Option.none => True
      | some t => (s.mv t).flags.released = true ∨
          (t ≠ i ∧ (s.mv t).mbuf ≠ k ∧ (s.mb (s.mv t).mbuf).master.obj ≠ some (.mv i))) :
    (pyBufferRelease b s).2.mv i = s.mv i ∧ (pyBufferRelease b s).2.mb k = s.mb k := by
  have zero : ∀ s' : St, (pyBufferRelease0 b s').2.mv i = s'.mv i ∧
      (pyBufferRelease0 b s').2.mb k = s'.mb k := by
    intro s'
    unfold pyBufferRelease0
    split
    · rename_i j hj
      have hne : j ≠ i := by
        rintro rfl
        exact hobj hj
      exact ⟨by simp only; exact St.mv_setMv_ne _ _ _ _ hne, rfl⟩
    · exact ⟨rfl, rfl⟩
  unfold pyBufferRelease
  split
  · rename_i t ht
    rw [ht] at h
    simp only at h
    dsimp only
    split
    · rcases h with hr | ⟨h1, h2, h3⟩
      · have e : memoryRelease0 t s = (.ok (), s) := by simp [memoryRelease0, hr]
        rw [e]
        exact zero s
      · obtain ⟨z1, z2⟩ := zero (memoryRelease0 t s).2
        obtain ⟨f1, f2⟩ := memoryRelease0_frame t i k s h1 h2 h3
        exact ⟨z1.trans f1, z2.trans f2⟩
    · exact zero s
  · exact zero s

/-- The release rules of `memoryview.release()` and `__exit__`
(Doc/library/stdtypes.rst, `release`; memoryobject.c:1104-1148). With exported buffers it
raises `BufferError("memoryview has N exported buffer(s)")` and changes nothing. With none
it marks the view released, takes it off the managed buffer's count, and the managed
buffer is released exactly when the count reaches zero; a second call changes nothing.
Hypotheses: `i` and its managed buffer are live objects, and a view is not the exporter of
its own managed buffer (type invariants), and `HookClear`, also a type invariant: when the
count reaches zero every view of the buffer is already released, and a view that is the
exporter of another buffer has exports, so it cannot be the one being released. -/
def ReleaseRules : Prop :=
  ∀ (st : St) (i : Nat), i < st.mvs.length → (st.mv i).mbuf < st.mbufs.length →
    (st.mb (st.mv i).mbuf).master.obj ≠ some (.mv i) → HookClear st i →
    let k := (st.mv i).mbuf
    let r := memoryviewRelease i st
    ((st.mv i).exports > 0 →
      r.1 = .error (bufferError s!"memoryview has {(st.mv i).exports} exported buffer{if (st.mv i).exports = 1 then "" else "s"}") ∧
      r.2 = st ∧ memoryExit i st = r) ∧
    ((st.mv i).exports = 0 → r.1 = .ok () ∧ baseInaccessible r.2 i = true ∧
      memoryviewRelease i r.2 = (.ok (), r.2) ∧
      ((st.mv i).flags.released = false →
        (r.2.mb k).exports = (st.mb k).exports - 1 ∧
        ((r.2.mb k).released = ((st.mb k).released || (st.mb k).exports == 1))))

theorem exports_setMv_self (st : St) (i : Nat) (x : MV) (hi : i < st.mvs.length) :
    (st.setMv i x).mv i = x := St.mv_setMv st i x hi

theorem second_release (s : St) (i : Nat) (h1 : (s.mv i).flags.released = true)
    (h2 : (s.mv i).exports = 0) :
    memoryviewRelease i s = (.ok (), s) ∧ baseInaccessible s i = true := by
  constructor
  · simp [memoryviewRelease, getExports, h2, memoryRelease, h1]
  · simp [baseInaccessible, h1]

theorem releaseRules_proven : ReleaseRules := by
  intro st i hi hk hself hclear
  dsimp only
  have hclear' := hclear
  unfold HookClear at hclear'
  generalize hx : st.mv i = x at *
  have hmr : ∀ h0 : x.exports = 0, memoryviewRelease i st = memoryRelease i st := by
    intro h0
    unfold memoryviewRelease getExports
    simp [hx, h0]
  constructor
  · intro hpos
    have h1 : ¬ x.exports = 0 := by omega
    have : memoryviewRelease i st = (.error (bufferError s!"memoryview has {x.exports} exported buffer{if x.exports = 1 then "" else "s"}"), st) := by
      unfold memoryviewRelease getExports
      simp [hx, h1, hpos]
    rw [this]
    exact ⟨rfl, rfl, by rw [← this]; rfl⟩
  · intro h0
    rw [hmr h0]
    by_cases hrel : x.flags.released = true
    · have e : memoryRelease i st = (.ok (), st) := by simp [memoryRelease, hx, hrel]
      rw [e]
      have := second_release st i (by rw [hx]; exact hrel) (by rw [hx]; exact h0)
      refine ⟨rfl, this.2, this.1, ?_⟩
      intro h; rw [hrel] at h; cases h
    · have hf : x.flags.released = false := by simpa using hrel
      generalize hy : ({ x with flags := { x.flags with released := true } } : MV) = y
      generalize hst1 : st.setMv i y = st1
      have hb : st1.mb x.mbuf = st.mb x.mbuf := by rw [← hst1]; rfl
      generalize hbb : st.mb x.mbuf = b at *
      generalize hst2 : st1.setMb x.mbuf { b with exports := b.exports - 1 } = st2
      have hk1 : x.mbuf < st1.mbufs.length := by rw [← hst1]; exact hk
      have hmv1 : st1.mv i = y := by rw [← hst1]; exact St.mv_setMv _ _ _ hi
      have hmv2 : st2.mv i = y := by rw [← hst2, St.mv_setMb]; exact hmv1
      have hmb2 : st2.mb x.mbuf = { b with exports := b.exports - 1 } := by
        rw [← hst2]; exact St.mb_setMb _ _ _ hk1
      have hyrel : y.flags.released = true := by rw [← hy]
      have hyexp : y.exports = 0 := by rw [← hy]; exact h0
      have hm : memoryRelease i st =
          (if b.exports - 1 = 0 then mbufRelease x.mbuf st2 else (.ok (), st2)) := by
        simp only [memoryRelease, hx, hf, Bool.false_eq_true, ↓reduceIte, hy, hst1, hb]
        simp only [hst2]
      rw [hm]
      by_cases he : b.exports - 1 = 0
      · rw [if_pos he]
        by_cases hc : b.released = true
        · have e2 : mbufRelease x.mbuf st2 = (.ok (), st2) := by
            simp [mbufRelease, hmb2, hc]
          rw [e2]
          have := second_release st2 i (by rw [hmv2]; exact hyrel) (by rw [hmv2]; exact hyexp)
          refine ⟨rfl, this.2, this.1, fun _ => ?_⟩
          rw [hmb2]
          simp [hc]
        · have hcf : b.released = false := by simpa using hc
          have hk2 : x.mbuf < st2.mbufs.length := by
            rw [← hst2]; simpa [St.setMb] using hk1
          have e2 : mbufRelease x.mbuf st2 =
              pyBufferRelease b.master (st2.setMb x.mbuf { b with exports := b.exports - 1, released := true }) := by
            simp [mbufRelease, hmb2, hcf]
          rw [e2]
          generalize hs3 : st2.setMb x.mbuf { b with exports := b.exports - 1, released := true } = s3
          have hmv3 : s3.mv i = y := by rw [← hs3, St.mv_setMb]; exact hmv2
          have hmb3 : s3.mb x.mbuf = { b with exports := b.exports - 1, released := true } := by
            rw [← hs3]; exact St.mb_setMb _ _ _ hk2
          have hself' : b.master.obj ≠ some (.mv i) := by
            rw [← hbb] at *
            exact hself
          have hmvs : ∀ t, t ≠ i → s3.mv t = st.mv t := by
            intro t ht
            rw [← hs3, St.mv_setMb, ← hst2, St.mv_setMb, ← hst1]
            exact St.mv_setMv_ne _ _ _ _ (Ne.symm ht)
          have hmbs : ∀ m, m ≠ x.mbuf → s3.mb m = st.mb m := by
            intro m hm
            rw [← hs3, St.mb_setMb_ne _ _ _ _ (Ne.symm hm), ← hst2, St.mb_setMb_ne _ _ _ _ (Ne.symm hm), ← hst1]
            rfl
          have hhook : (match b.master.hook with
              | Option.none => True
              | some t => (s3.mv t).flags.released = true ∨
                  (t ≠ i ∧ (s3.mv t).mbuf ≠ x.mbuf ∧
                    (s3.mb (s3.mv t).mbuf).master.obj ≠ some (.mv i))) := by
            split
            · exact trivial
            · rename_i t ht
              rw [ht] at hclear'
              simp only at hclear'
              by_cases hti : t = i
              · subst hti
                exact Or.inl (by rw [hmv3]; exact hyrel)
              · rcases hclear' with hr | ⟨h1, h2, h3⟩
                · exact Or.inl (by rw [hmvs t hti]; exact hr)
                · refine Or.inr ⟨h1, ?_, ?_⟩
                  · rw [hmvs t hti]; exact h2
                  · rw [hmvs t hti, hmbs _ h2]; exact h3
          obtain ⟨hmv4', hmb4⟩ := hook_frame b.master s3 i x.mbuf hself' hhook
          have hmv4 : (pyBufferRelease b.master s3).2.mv i = y := hmv4'.trans hmv3
          have := second_release (pyBufferRelease b.master s3).2 i
            (by rw [hmv4]; exact hyrel) (by rw [hmv4]; exact hyexp)
          have hres : (pyBufferRelease b.master s3).1 = .ok () := pyBufferRelease_ok _ _
          refine ⟨hres, this.2, this.1, fun _ => ?_⟩
          rw [hmb4, hmb3]
          have : b.exports = 1 := by omega
          simp [this]
      · rw [if_neg he]
        have := second_release st2 i (by rw [hmv2]; exact hyrel) (by rw [hmv2]; exact hyexp)
        refine ⟨rfl, this.2, this.1, fun _ => ?_⟩
        rw [hmb2]
        have : ¬ b.exports = 1 := by omega
        simp [this]

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
