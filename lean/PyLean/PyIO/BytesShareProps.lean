import PyLean.PyIO.BytesShare

/-!
Properties of `io.BytesIO`'s shared buffer (`PyIO/BytesShare.lean`):

* `BytesIOHeldImmutable`: no operation changes a `bytes` object the program holds,
  which is what the unshares before an in-place write (bytesio.c:264-269), in a resize
  (:214-217) and before an export (:1243-1246), and the export checks of the zero-copy
  returns (:417, :478), are for.
* `BytesIOZeroCopy`: `getvalue()` and a whole-buffer `read()` return the buffer object
  itself when no view exists, and a new object otherwise.
* `BytesIOGetbufferLive`: a `getbuffer()` view reads and writes the stream's contents,
  and blocks every write, truncate and close while it lives.
* `BytesIOHashConsistent` (refuted): every `bytes` object the program holds hashes as
  its contents. 3.15.2 writes in place into a buffer whose hash was cached while the
  program held it (gh-160181, fixed on main by `HASHED_BUF`).
-/

namespace PyLean.PyIO.Share

open PyLean PyLean.PyIO

/-! ## Field lemmas -/

namespace St

@[simp] theorem newObj_held (st : St) (d : List Nat) : (st.newObj d).held = st.held := rfl
@[simp] theorem newObj_buf (st : St) (d : List Nat) : (st.newObj d).buf = st.buf := rfl
@[simp] theorem newObj_views (st : St) (d : List Nat) : (st.newObj d).views = st.views := rfl
@[simp] theorem newObj_size (st : St) (d : List Nat) : (st.newObj d).size = st.size := rfl
@[simp] theorem newObj_pos (st : St) (d : List Nat) : (st.newObj d).pos = st.pos := rfl
@[simp] theorem newObj_next (st : St) (d : List Nat) : (st.newObj d).next = st.next + 1 := rfl

@[simp] theorem setData_held (st : St) (r : Ref) (d : List Nat) : (st.setData r d).held = st.held := by
  cases r <;> rfl
@[simp] theorem setData_buf (st : St) (r : Ref) (d : List Nat) : (st.setData r d).buf = st.buf := by
  cases r <;> rfl
@[simp] theorem setData_views (st : St) (r : Ref) (d : List Nat) : (st.setData r d).views = st.views := by
  cases r <;> rfl
@[simp] theorem setData_size (st : St) (r : Ref) (d : List Nat) : (st.setData r d).size = st.size := by
  cases r <;> rfl
@[simp] theorem setData_pos (st : St) (r : Ref) (d : List Nat) : (st.setData r d).pos = st.pos := by
  cases r <;> rfl
@[simp] theorem setData_next (st : St) (r : Ref) (d : List Nat) : (st.setData r d).next = st.next := by
  cases r <;> rfl

theorem newObj_data_old (st : St) (d : List Nat) (r : Ref) (h : ∀ i, r = .heap i → i < st.next) :
    (st.newObj d).data r = st.data r := by
  cases r with
  | single => rfl
  | heap i =>
    have := h i rfl
    have hne : i ≠ st.next := by omega
    simp [newObj, data, hne]

theorem newObj_data_new (st : St) (d : List Nat) : (st.newObj d).data (.heap st.next) = d := by
  simp [newObj, data]

theorem setData_data_other (st : St) (r : Ref) (d : List Nat) (r' : Ref) (h : r' ≠ r) :
    (st.setData r d).data r' = st.data r' := by
  cases r with
  | single => rfl
  | heap i =>
    cases r' with
    | single => rfl
    | heap j =>
      have : j ≠ i := fun e => h (by rw [e])
      simp [setData, data, this]

theorem setData_data_self (st : St) (i : Nat) (d : List Nat) : (st.setData (.heap i) d).data (.heap i) = d := by
  simp [setData, data]

/-- The contents do not depend on the scalar fields. -/
@[simp] theorem data_pos (st : St) (p : Nat) (r : Ref) : ({ st with pos := p } : St).data r = st.data r := by
  cases r <;> rfl
@[simp] theorem data_size (st : St) (n : Nat) (r : Ref) : ({ st with size := n } : St).data r = st.data r := by
  cases r <;> rfl
@[simp] theorem data_pos_size (st : St) (p n : Nat) (r : Ref) :
    ({ st with pos := p, size := n } : St).data r = st.data r := by
  cases r <;> rfl
@[simp] theorem data_held (st : St) (h : List Ref) (r : Ref) : ({ st with held := h } : St).data r = st.data r := by
  cases r <;> rfl
@[simp] theorem data_views (st : St) (v : List (Option View)) (r : Ref) :
    ({ st with views := v } : St).data r = st.data r := by
  cases r <;> rfl
@[simp] theorem data_buf (st : St) (b : Option Ref) (r : Ref) : ({ st with buf := b } : St).data r = st.data r := by
  cases r <;> rfl

end St

theorem liveCount_zero {vs : List (Option View)} (h : liveCount vs = 0) : ∀ w, some w ∉ vs := by
  intro w hw
  have := List.countP_eq_zero.1 h (some w) hw
  simp at this

theorem liveCount_pos {vs : List (Option View)} (h : 0 < liveCount vs) : ∃ w, some w ∈ vs := by
  obtain ⟨a, ha, hs⟩ := List.countP_pos_iff.1 h
  cases a with
  | none => simp at hs
  | some w => exact ⟨w, ha⟩

theorem liveCount_append (vs : List (Option View)) (w : View) :
    liveCount (vs ++ [some w]) = liveCount vs + 1 := by
  simp [liveCount, List.countP_append]

theorem set_append_last {α : Type} : ∀ (l : List α) (a b : α), (l ++ [a]).set l.length b = l ++ [b]
  | [], _, _ => rfl
  | x :: xs, a, b => by simp [set_append_last xs a b]

theorem getElem?_append_last {α : Type} (l : List α) (a : α) : (l ++ [a])[l.length]? = some a := by
  simp

/-! ## The invariant -/

/-- What every reachable state satisfies: heap references are allocated, and every live
view is over `self->buf`, `string_size` bytes long, over an object the program does not
hold, and over a singleton only when empty. -/
structure Inv (st : St) : Prop where
  held : ∀ i, Ref.heap i ∈ st.held → i < st.next
  buf : ∀ i, st.buf = some (.heap i) → i < st.next
  views : ∀ w, some w ∈ st.views → st.buf = some w.target ∧ w.len = st.size ∧
    (∀ i, w.target = .heap i → Ref.heap i ∉ st.held) ∧ (∀ d, w.target = .single d → w.len = 0)

/-- What an unshare or a resize preserves. -/
structure Frame (st st' : St) : Prop where
  held : st'.held = st.held
  views : st'.views = st.views
  size : st'.size = st.size
  pos : st'.pos = st.pos
  next : st.next ≤ st'.next
  keep : ∀ r ∈ st.held, st'.data r = st.data r
  buf : ∀ i, st'.buf = some (.heap i) → i < st'.next

/-- The new `self->buf` is not held by the program. -/
def Fresh (st st' : St) : Prop := ∀ i, st'.buf = some (.heap i) → Ref.heap i ∉ st.held

theorem frame_refl {st : St} (hI : Inv st) : Frame st st :=
  ⟨rfl, rfl, rfl, rfl, Nat.le_refl _, fun _ _ => rfl, hI.buf⟩

theorem fresh_unshared {st : St} {r : Ref} (hb : st.buf = some r) (hs : st.shared r = false) : Fresh st st := by
  intro i h
  rw [hb] at h
  cases h
  simpa [St.shared] using hs

theorem frame_newObj {st : St} (hI : Inv st) (d : List Nat) :
    Frame st { st.newObj d with buf := some (.heap st.next) } ∧ Fresh st { st.newObj d with buf := some (.heap st.next) } := by
  refine ⟨⟨rfl, rfl, rfl, rfl, by simp, fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [St.data_buf]
    exact St.newObj_data_old _ _ _ (fun i hi => hI.held i (hi ▸ hr))
  · intro i h; simp at h; simp [h]
  · intro i h hm
    simp at h
    have := hI.held i hm
    omega

theorem frame_single (st : St) (d : List Nat) :
    Frame st { st with buf := some (.single d) } ∧ Fresh st { st with buf := some (.single d) } :=
  ⟨⟨rfl, rfl, rfl, rfl, Nat.le_refl _, fun _ _ => rfl, by simp⟩, by intro i h; simp at h⟩

theorem unshare_spec {st st' : St} {n : Nat} (hI : Inv st) (e : unshare st n = .ok st') :
    Frame st st' ∧ Fresh st st' ∧ (∀ d, st'.buf = some (.single d) → n = 0) := by
  unfold unshare at e
  split at e
  · cases e
    exact ⟨frame_refl hI, by intro i h; simp_all, fun _ h => by simp_all⟩
  · split at e
    · cases e
    · split at e
      · cases e
        exact ⟨(frame_single st []).1, (frame_single st []).2, fun _ _ => by assumption⟩
      · split at e
        · cases e
        · cases e
          exact ⟨(frame_newObj hI _).1, (frame_newObj hI _).2, fun d h => by simp at h⟩

theorem resizeUnshared_spec {st st' : St} {r : Ref} {n : Int} (hI : Inv st) (hb : st.buf = some r)
    (hs : st.shared r = false) (e : resizeUnshared st n = .ok st') : Frame st st' ∧ Fresh st st' := by
  unfold resizeUnshared at e
  rw [hb] at e
  simp only at e
  split at e
  · cases e
  · split at e
    · cases e; exact ⟨frame_refl hI, fresh_unshared hb hs⟩
    · split at e
      · split at e
        · cases e
        · cases e; exact frame_newObj hI _
      · split at e
        · cases e; exact frame_single st []
        · split at e
          · split at e
            · cases e
            · cases e; exact frame_newObj hI _
          · split at e
            · cases e
            · cases e
              have hr : ∀ x ∈ st.held, x ≠ r := by
                intro x hx hxr
                subst hxr
                cases x with
                | single => simp [St.shared] at hs
                | heap i => simp [St.shared] at hs; exact hs hx
              refine ⟨⟨by simp, by simp, by simp, by simp, by simp, fun x hx => St.setData_data_other _ _ _ _ (hr x hx),
                ?_⟩, ?_⟩
              · intro i h; simp at h; simpa using hI.buf i h
              · intro i h; simp at h; exact fresh_unshared hb hs i h

theorem resizeBuffer_spec {st st' : St} {n : Nat} (hI : Inv st) (e : resizeBuffer st n = .ok st') :
    Frame st st' ∧ (newAlloc st.alloc n ≠ none → Fresh st st') := by
  unfold resizeBuffer at e
  split at e
  · cases e
  · split at e
    · rename_i h; cases e; exact ⟨frame_refl hI, fun h' => absurd h h'⟩
    · split at e
      · cases e; exact ⟨frame_refl hI, fun _ i h => by simp_all⟩
      · rename_i r hb
        split at e
        · have := unshare_spec hI e; exact ⟨this.1, fun _ => this.2.1⟩
        · rename_i hs
          have := resizeUnshared_spec hI hb (by simpa using hs) e
          exact ⟨this.1, fun _ => this.2⟩

theorem newAlloc_grow {alloc n : Nat} (h : alloc < n) : newAlloc alloc n ≠ none := by
  unfold newAlloc
  have h1 : ¬ n < alloc / 2 := by omega
  have h2 : ¬ n < alloc := by omega
  simp only [h1, h2, ite_false]
  split <;> simp

/-! ## One step keeps held objects and the invariant -/

/-- No held object changed. -/
def Keeps (st st' : St) : Prop := ∀ r ∈ st.held, st'.data r = st.data r

theorem inv_noviews {st : St} (h0 : st.exports = 0) (st' : St)
    (hh : ∀ i, Ref.heap i ∈ st'.held → i < st'.next) (hb : ∀ i, st'.buf = some (.heap i) → i < st'.next)
    (hv : st'.views = st.views) : Inv st' :=
  ⟨hh, hb, fun w hw => absurd (hv ▸ hw) (liveCount_zero h0 w)⟩

/-- Keeping a returned reference. -/
def PushOk (st : St) (r : Ref) : Prop :=
  (∀ i, r = .heap i → i < st.next) ∧ (∀ w, some w ∈ st.views → ∀ i, w.target = .heap i → r ≠ .heap i)

theorem inv_push {st : St} (hI : Inv st) {r : Ref} (hp : PushOk st r) :
    Inv { st with held := st.held ++ [r] } := by
  refine ⟨fun i h => ?_, hI.buf, fun w hw => ?_⟩
  · simp only [List.mem_append, List.mem_singleton] at h
    rcases h with h | h
    · exact hI.held i h
    · exact hp.1 i h.symm
  · obtain ⟨a, b, c, d⟩ := hI.views w hw
    refine ⟨a, b, fun i hi hm => ?_, d⟩
    simp only [List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | hm
    · exact c i hi hm
    · exact hp.2 w hw i hi hm.symm

theorem keeps_push {st st' : St} (h : Keeps st st') (r : Ref) : Keeps st { st' with held := st'.held ++ [r] } := by
  intro x hx; simp only [St.data_held]; exact h x hx

/-- A copy (`PyBytes_FromStringAndSize`) of anything: the old objects are untouched and the
result can be kept. -/
theorem fromBytes_spec {st : St} (hI : Inv st) (d : List Nat) :
    Keeps st (st.fromBytes d).1 ∧ Inv (st.fromBytes d).1 ∧ PushOk (st.fromBytes d).1 (st.fromBytes d).2 ∧
    (st.fromBytes d).1.held = st.held ∧ (st.fromBytes d).1.buf = st.buf ∧ (st.fromBytes d).1.views = st.views ∧
    (st.fromBytes d).1.pos = st.pos ∧ (st.fromBytes d).1.size = st.size := by
  unfold St.fromBytes
  split
  · exact ⟨fun _ _ => rfl, hI, ⟨fun i h => by simp at h, fun w _ i _ h => by simp at h⟩, rfl, rfl, rfl, rfl, rfl⟩
  · refine ⟨fun r hr => St.newObj_data_old _ _ _ (fun i hi => hI.held i (hi ▸ hr)),
      ⟨fun i h => ?_, fun i h => ?_, fun w hw => ?_⟩, ⟨fun i h => ?_, fun w hw i hi h => ?_⟩, rfl, rfl, rfl, rfl, rfl⟩
    · have := hI.held i h; simp; omega
    · have := hI.buf i h; simp; omega
    · exact hI.views w hw
    · simp at h; simp [h]
    · simp at h; subst h
      obtain ⟨hb, _⟩ := hI.views w hw
      rw [hi] at hb
      have := hI.buf _ hb
      omega

theorem readBytes_spec {st : St} (hI : Inv st) (n : Nat) :
    Keeps st (readBytes st n).1 ∧ Inv (readBytes st n).1 ∧ PushOk (readBytes st n).1 (readBytes st n).2 ∧
    (readBytes st n).1.held = st.held := by
  unfold readBytes
  split
  · exact ⟨fun _ _ => rfl, hI, ⟨fun i h => by simp at h, fun w _ i _ h => by simp at h⟩, rfl⟩
  · rename_i r hb
    split
    · rename_i hc
      refine ⟨fun _ _ => by simp, ⟨hI.held, hI.buf, fun w hw => ?_⟩, ⟨fun i h => ?_, fun w hw => ?_⟩, rfl⟩
      · exact absurd hw (liveCount_zero hc.2.2.2 w)
      · simp only; exact hI.buf i (h ▸ hb)
      · exact absurd hw (liveCount_zero hc.2.2.2 w)
    · split
      · exact ⟨fun _ _ => rfl, hI, ⟨fun i h => by simp at h, fun w _ i _ h => by simp at h⟩, rfl⟩
      · obtain ⟨k, hi, hp, hh, hbf, hv, _, _⟩ := fromBytes_spec hI (slice (st.data r) st.pos n)
        refine ⟨fun x hx => by simp only [St.data_pos]; exact k x hx, ⟨fun i h => hi.held i h, fun i h => hi.buf i h,
          fun w hw => ?_⟩, ⟨hp.1, hp.2⟩, hh⟩
        obtain ⟨a, b, c, d⟩ := hi.views w hw
        exact ⟨a, by rw [b], c, d⟩

theorem writePrep_spec {st st1 : St} {r : Ref} {endpos : Nat} (hI : Inv st) (hb : st.buf = some r)
    (e : writePrep st r endpos = .ok st1) : Frame st st1 ∧ Fresh st st1 := by
  unfold writePrep at e
  split at e
  · rename_i hg
    have hf := resizeBuffer_spec hI e
    refine ⟨hf.1, hf.2 (newAlloc_grow ?_)⟩
    simp only [St.alloc, hb]; omega
  · split at e
    · have := unshare_spec hI e; exact ⟨this.1, this.2.1⟩
    · rename_i hs; cases e; exact ⟨frame_refl hI, fresh_unshared hb (by simpa using hs)⟩

theorem writeInto_spec {st st1 : St} (hI : Inv st) (h0 : st.exports = 0) (hf : Frame st st1)
    (hfr : Fresh st st1) (b : List Nat) : Keeps st (writeInto st st1 b).1 ∧ Inv (writeInto st st1 b).1 := by
  unfold writeInto
  split
  · exact ⟨fun _ _ => rfl, hI⟩
  · rename_i r1 hb1
    refine ⟨fun x hx => ?_, ?_⟩
    · simp only [St.data_pos_size]
      cases r1 with
      | single => exact hf.keep x hx
      | heap j =>
        have hne : x ≠ .heap j := fun e' => hfr j hb1 (e' ▸ hx)
        rw [St.setData_data_other _ _ _ _ hne, hf.keep x hx]
    · refine inv_noviews h0 _ (fun i h => ?_) (fun i h => ?_) (by simp [hf.views])
      · simp only [St.setData_held, hf.held] at h; have := hI.held i h; have := hf.next; simp; omega
      · simp only [St.setData_buf] at h; simpa using hf.buf i h

theorem write_spec {st : St} (hI : Inv st) (b : List Nat) : Keeps st (write st b).1 ∧ Inv (write st b).1 := by
  unfold write
  split
  · exact ⟨fun _ _ => rfl, hI⟩
  · rename_i r hb
    split
    · exact ⟨fun _ _ => rfl, hI⟩
    · rename_i hex
      split
      · exact ⟨fun _ _ => rfl, hI⟩
      · split
        · exact ⟨fun _ _ => rfl, hI⟩
        · rename_i st1 e
          obtain ⟨hf, hfr⟩ := writePrep_spec hI hb e
          exact writeInto_spec hI (by omega) hf hfr b

theorem sizePrep_spec {st st1 : St} {r : Ref} (hI : Inv st) (hb : st.buf = some r)
    (e : sizePrep st r = .ok st1) : Frame st st1 := by
  unfold sizePrep at e
  split at e
  · split at e
    · exact (unshare_spec hI e).1
    · rename_i hs; exact (resizeUnshared_spec hI hb (by simpa using hs) e).1
  · cases e; exact frame_refl hI

theorem getvalue_spec {st : St} (hI : Inv st) : Keeps st (getvalue st).1 ∧ Inv (getvalue st).1 := by
  unfold getvalue
  split
  · exact ⟨fun _ _ => rfl, hI⟩
  · rename_i r hb
    split
    · obtain ⟨k, hi, hp, hh, _⟩ := fromBytes_spec hI ((st.data r).take st.size)
      refine ⟨fun x hx => by simp only [St.data_held]; exact k x hx, ?_⟩
      have := inv_push hi hp
      rw [hh] at this
      exact this
    · rename_i hc
      have h0 : st.exports = 0 := by omega
      split
      · exact ⟨fun _ _ => rfl, hI⟩
      · rename_i st1 e
        have hf := sizePrep_spec hI hb e
        split
        · exact ⟨fun _ _ => rfl, hI⟩
        · rename_i r1 hb1
          refine ⟨fun x hx => by simp only [St.data_held]; exact hf.keep x hx, ?_⟩
          refine inv_noviews h0 _ (fun i h => ?_) (fun i h => ?_) (by simp [hf.views])
          · show i < st1.next
            simp only [List.mem_append, List.mem_singleton, hf.held] at h
            rcases h with h | h
            · have := hI.held i h; have := hf.next; omega
            · exact hf.buf i (h ▸ hb1)
          · exact hf.buf i h

theorem keepRes_spec {st st' : St} {r : Ref} (hk : Keeps st st') (hi : Inv st') (hp : PushOk st' r) :
    Keeps st (keepRes st' r).1 ∧ Inv (keepRes st' r).1 := by
  unfold keepRes
  exact ⟨keeps_push hk r, inv_push hi hp⟩

theorem read_spec {st : St} (hI : Inv st) (n : Option Int) : Keeps st (read st n).1 ∧ Inv (read st n).1 := by
  unfold read
  split
  · exact ⟨fun _ _ => rfl, hI⟩
  · split
    · exact ⟨fun _ _ => rfl, hI⟩
    · rename_i m _ _
      have := readBytes_spec hI
        (if m < 0 ∨ m > (st.size : Int) - st.pos then (if (st.size : Int) - st.pos < 0 then 0 else (st.size : Int) - st.pos) else m).toNat
      exact keepRes_spec this.1 this.2.1 this.2.2.1

theorem readline_spec {st : St} (hI : Inv st) (n : Option Int) : Keeps st (readline st n).1 ∧ Inv (readline st n).1 := by
  unfold readline
  split
  · exact ⟨fun _ _ => rfl, hI⟩
  · split
    · exact ⟨fun _ _ => rfl, hI⟩
    · rename_i m _ _
      have := readBytes_spec hI (C.scanEol st.proj m)
      exact keepRes_spec this.1 this.2.1 this.2.2.1

theorem truncate_spec {st : St} (hI : Inv st) (n : Option Int) : Keeps st (truncate st n).1 ∧ Inv (truncate st n).1 := by
  unfold truncate
  split
  · exact ⟨fun _ _ => rfl, hI⟩
  · split
    · exact ⟨fun _ _ => rfl, hI⟩
    · rename_i hex
      have h0 : st.exports = 0 := by omega
      split
      · exact ⟨fun _ _ => rfl, hI⟩
      · rename_i m _
        split
        · exact ⟨fun _ _ => rfl, hI⟩
        · split
          · have hI' : Inv { st with size := m.toNat } :=
              ⟨hI.held, hI.buf, fun w hw => absurd hw (liveCount_zero h0 w)⟩
            split
            · exact ⟨fun _ _ => rfl, hI⟩
            · rename_i st1 e
              have hf := (resizeBuffer_spec hI' e).1
              refine ⟨fun x hx => by rw [hf.keep x hx]; simp, ?_⟩
              exact inv_noviews h0 _ (fun i h => by rw [hf.held] at h; exact Nat.lt_of_lt_of_le (hI.held i h) hf.next)
                hf.buf hf.views
          · exact ⟨fun _ _ => rfl, hI⟩

theorem getbuffer_spec {st : St} (hI : Inv st) : Keeps st (getbuffer st).1 ∧ Inv (getbuffer st).1 := by
  unfold getbuffer
  split
  · exact ⟨fun _ _ => rfl, hI⟩
  · rename_i r hb
    split
    · exact ⟨fun _ _ => rfl, hI⟩
    · rename_i st1 e
      split
      · exact ⟨fun _ _ => rfl, hI⟩
      · rename_i r1 hb1
        unfold exportPrep at e
        split at e
        · -- the first view of a shared buffer: a fresh copy
          rename_i hc
          obtain ⟨hf, hfr, hsg⟩ := unshare_spec hI e
          refine ⟨fun x hx => by simp only [St.data_views]; exact hf.keep x hx, ⟨?_, ?_, fun w hw => ?_⟩⟩
          · intro i h; simp only [hf.held] at h; exact Nat.lt_of_lt_of_le (hI.held i h) hf.next
          · intro i h; exact hf.buf i h
          · simp only [List.mem_append, List.mem_singleton, hf.views] at hw
            rcases hw with hw | hw
            · exact absurd hw (liveCount_zero hc.1 w)
            · cases hw
              refine ⟨hb1, rfl, fun i hi => ?_, fun d hd => ?_⟩
              · simp only [hf.held]; exact hfr i (hi ▸ hb1)
              · simp only at hd ⊢
                rw [hd] at hb1
                rw [hf.size]; exact hsg d hb1
        · rename_i hc
          cases e
          rw [hb] at hb1; cases hb1
          refine ⟨fun _ _ => rfl, ⟨hI.held, hI.buf, fun w hw => ?_⟩⟩
          simp only [List.mem_append, List.mem_singleton] at hw
          rcases hw with hw | hw
          · exact hI.views w hw
          · cases hw
            by_cases h0 : st.exports = 0
            · have hs : st.shared r = false := by simpa [h0] using hc
              refine ⟨hb, rfl, fun i hi => ?_, fun d hd => ?_⟩
              · exact fresh_unshared hb hs i (hi ▸ hb)
              · simp only at hd; subst hd; simp [St.shared] at hs
            · obtain ⟨w, hw⟩ := liveCount_pos (Nat.pos_of_ne_zero h0)
              obtain ⟨hwb, hwl, hwh, hws⟩ := hI.views w hw
              rw [hb] at hwb; cases hwb
              exact ⟨hb, rfl, hwh, fun d hd => by rw [← hwl]; exact hws d hd⟩

theorem viewSet_spec {st : St} (hI : Inv st) (v i x : Nat) : Keeps st (viewSet st v i x).1 ∧ Inv (viewSet st v i x).1 := by
  unfold viewSet
  split
  · rename_i w hw
    have hmem : some w ∈ st.views := List.mem_of_getElem? hw
    obtain ⟨_, _, hwh, _⟩ := hI.views w hmem
    split
    · split
      · refine ⟨fun r hr => ?_, ⟨by simpa using hI.held, by simpa using hI.buf,
          fun w' hw' => by simpa using hI.views w' (by simpa using hw')⟩⟩
        cases hwt : w.target with
        | single d => rfl
        | heap j =>
          show (st.setData (Ref.heap j) _).data r = st.data r
          refine St.setData_data_other _ _ _ _ (fun e => hwh j hwt ?_)
          rw [← e]; exact hr
      · exact ⟨fun _ _ => rfl, hI⟩
    · exact ⟨fun _ _ => rfl, hI⟩
  · exact ⟨fun _ _ => rfl, hI⟩

theorem release_spec {st : St} (hI : Inv st) (v : Nat) : Keeps st (release st v).1 ∧ Inv (release st v).1 := by
  unfold release
  split
  · refine ⟨fun _ _ => by simp, ⟨hI.held, hI.buf, fun w hw => ?_⟩⟩
    rcases List.mem_or_eq_of_mem_set hw with h | h
    · exact hI.views w h
    · cases h
  · exact ⟨fun _ _ => rfl, hI⟩

theorem hashOp_spec {st : St} (hI : Inv st) (h : Nat) : Keeps st (hashOp st h).1 ∧ Inv (hashOp st h).1 := by
  unfold hashOp
  split
  · rename_i i _
    refine ⟨fun r _ => ?_, ⟨hI.held, hI.buf, hI.views⟩⟩
    cases r with
    | single => rfl
    | heap j => by_cases e : j = i <;> simp [St.data, e]
  · exact ⟨fun _ _ => rfl, hI⟩

theorem step_spec {st : St} (hI : Inv st) (op : SOp) : Keeps st (step st op).1 ∧ Inv (step st op).1 := by
  cases op with
  | write b => exact write_spec hI b
  | getvalue => exact getvalue_spec hI
  | read n => exact read_spec hI n
  | readline n => exact readline_spec hI n
  | seek p w => exact ⟨fun _ _ => by simp [step], ⟨hI.held, hI.buf, hI.views⟩⟩
  | tell => simp only [step]; split <;> exact ⟨fun _ _ => rfl, hI⟩
  | truncate n => exact truncate_spec hI n
  | getbuffer => exact getbuffer_spec hI
  | viewSet v i x => exact viewSet_spec hI v i x
  | viewBytes v => simp only [step, viewBytes]; split <;> exact ⟨fun _ _ => rfl, hI⟩
  | release v => exact release_spec hI v
  | close =>
    simp only [step]
    split
    · exact ⟨fun _ _ => rfl, hI⟩
    · exact ⟨fun _ _ => by simp, inv_noviews (st := st) (by omega) _ hI.held (by simp) rfl⟩
  | closed => exact ⟨fun _ _ => rfl, hI⟩
  | drop h =>
    refine ⟨fun _ _ => by simp [step], ⟨fun i hm => hI.held i (List.mem_of_mem_eraseIdx hm), hI.buf, fun w hw => ?_⟩⟩
    obtain ⟨a, b, c, d⟩ := hI.views w hw
    exact ⟨a, b, fun i hi hm => c i hi (List.mem_of_mem_eraseIdx hm), d⟩
  | hash h => exact hashOp_spec hI h
  | same h k => exact ⟨fun _ _ => rfl, hI⟩

theorem start_inv (init : List Nat) (keep : Bool) : Inv (start init keep) := by
  refine ⟨fun i h => ?_, fun i h => ?_, fun w hw => by simp [start] at hw⟩
  · simp only [start] at h ⊢
    by_cases h1 : init.length ≤ 1 <;> cases keep <;> simp [h1] at h <;> omega
  · simp only [start] at h ⊢
    by_cases h1 : init.length ≤ 1 <;> simp [h1] at h <;> omega

theorem runOps_fst_cons {σ ω : Type} (step : σ → ω → σ × Py Val) (s : σ) (o : ω) (os : List ω) :
    (runOps step s (o :: os)).1 = (runOps step (step s o).1 os).1 := by
  simp [runOps]

theorem run_inv : ∀ (ops : List SOp) (st : St), Inv st → Inv (runOps step st ops).1
  | [], _, h => h
  | o :: os, st, h => by rw [runOps_fst_cons]; exact run_inv os _ (step_spec h o).2

/-! ## The statements -/

/-- `bytes` are immutable: in every state a program can reach, whatever it did with
`getvalue`, `read`, `readline`, the initial value, views, hashes and `del`, no operation
changes the contents of a `bytes` object the program holds. This is what the copies
before an in-place write, in a resize and before an export, and the export checks of
the zero-copy returns, are for: drop any of them and a held object changes. -/
def BytesIOHeldImmutable : Prop := ∀ (init : List Nat) (keep : Bool) (ops : List SOp) (op : SOp),
  ∀ r ∈ (runS init keep ops).1.held, (step (runS init keep ops).1 op).1.data r = (runS init keep ops).1.data r

theorem bytesIOHeldImmutable_proven : BytesIOHeldImmutable := by
  intro init keep ops op r hr
  exact (step_spec (run_inv ops _ (start_inv init keep)) op).1 r hr

/-! ### Zero-copy returns -/

theorem allocBytes_ok {n : Nat} (hm : n < memLimit) : allocBytes n = .ok () := by
  have h1 : (memLimit : Int) ≤ ssizeMax - 33 := by decide
  unfold allocBytes
  have a : ¬ (n : Int) > ssizeMax - 33 := by omega
  have b : ¬ (n : Int) ≥ (memLimit : Int) := by omega
  simp only [a, b, ite_false]

theorem ssize_ok {n : Nat} (hm : n < memLimit) : ¬ (n : Int) > ssizeMax := by
  have h1 : (memLimit : Int) ≤ ssizeMax := by decide
  omega

/-- `getvalue`'s sizing (bytesio.c:421-430) succeeds below the allocation bound and leaves
`self->buf` holding exactly the contents. -/
theorem sizePrep_ok {st : St} {r : Ref} (hb : st.buf = some r) (hle : st.size ≤ (st.data r).length)
    (hm : st.size < memLimit) (h2 : 2 ≤ st.size) :
    ∃ st1 r1, sizePrep st r = .ok st1 ∧ st1.buf = some r1 ∧ st1.data r1 = (st.data r).take st.size ∧
      st1.held = st.held := by
  unfold sizePrep
  by_cases hs : st.size ≠ (st.data r).length
  · rw [if_pos hs]
    by_cases hsh : st.shared r = true
    · rw [if_pos hsh]
      unfold unshare
      rw [hb]
      have hz : st.size ≠ 0 := by omega
      simp only [ssize_ok hm, hz, ite_false, allocBytes_ok hm]
      refine ⟨_, _, rfl, rfl, ?_, rfl⟩
      simp only [St.data_buf, St.newObj_data_new, Nat.sub_self, List.replicate_zero, List.append_nil]
    · rw [if_neg hsh]
      unfold resizeUnshared
      rw [hb]
      simp only
      have hn : ¬ (st.size : Int) < 0 := by omega
      have e1 : (st.size : Int).toNat = st.size := by omega
      have h3 : ¬ (st.data r).length = st.size := fun e => hs e.symm
      have h4 : ¬ (st.data r).length = 0 := by omega
      have h5 : ¬ st.size = 0 := by omega
      have hsub : st.size - (st.data r).length = 0 := by omega
      simp only [hn, ite_false, e1, h3, h4, h5, allocBytes_ok hm, hsub, List.replicate_zero, List.append_nil]
      have hsf : st.shared r = false := by simpa using hsh
      split
      · exact ⟨_, _, rfl, rfl, by simp [St.data, St.newObj], rfl⟩
      · cases r with
        | single => simp [St.shared] at hsf
        | heap i => exact ⟨_, _, rfl, by simp [hb], St.setData_data_self _ _ _, by simp⟩
  · rw [if_neg hs]
    have : st.size = (st.data r).length := by omega
    exact ⟨st, r, rfl, hb, by rw [this, List.take_length], rfl⟩

/-- `getvalue()` returns `self->buf` itself when no view exists and it holds at least two
bytes (bytesio.c:421-432), first sized to the contents; otherwise a new object, or a
singleton for at most one byte (:417-419), and `self->buf` stays. A whole-buffer `read()`
from position 0 likewise returns `self->buf` with no view (:476-482) and a new object
with one. Hypotheses: the state is reachable (`Inv`), `string_size` fits the allocation
(type invariant) and is below the allocation bound. -/
def BytesIOZeroCopy : Prop := ∀ (st : St) (r : Ref), Inv st → st.buf = some r →
    st.size ≤ (st.data r).length → st.size < memLimit →
  ((st.exports = 0 → 2 ≤ st.size →
      (getvalue st).2 = .ok (.bytes ((st.data r).take st.size)) ∧
      ∃ r', (getvalue st).1.held = st.held ++ [r'] ∧ (getvalue st).1.buf = some r') ∧
   (0 < st.exports ∨ st.size ≤ 1 →
      (getvalue st).2 = .ok (.bytes ((st.data r).take st.size)) ∧ (getvalue st).1.buf = st.buf ∧
      ∃ r', (getvalue st).1.held = st.held ++ [r'] ∧ (∀ i, r' = .heap i → st.next ≤ i))) ∧
  (st.pos = 0 → st.size = (st.data r).length → 2 ≤ st.size →
    (st.exports = 0 → (read st none).1.held = st.held ++ [r] ∧ (read st none).2 = .ok (.bytes (st.data r))) ∧
    (0 < st.exports → (read st none).2 = .ok (.bytes (st.data r)) ∧
      ∃ r', (read st none).1.held = st.held ++ [r'] ∧ (∀ i, r' = .heap i → st.next ≤ i)))

theorem bytesIOZeroCopy_proven : BytesIOZeroCopy := by
  intro st r hI hb hle hm
  refine ⟨⟨fun h0 h2 => ?_, fun hc => ?_⟩, fun hp hl h2 => ⟨fun h0 => ?_, fun hx => ?_⟩⟩
  · obtain ⟨st1, r1, e, hb1, hd, hh⟩ := sizePrep_ok hb hle hm h2
    have hc : ¬ (st.size ≤ 1 ∨ st.exports > 0) := by omega
    unfold getvalue
    rw [hb]
    simp only [hc, ite_false, e, hb1, hd]
    exact ⟨by simp, r1, by rw [hh], rfl⟩
  · have hc' : st.size ≤ 1 ∨ st.exports > 0 := by omega
    unfold getvalue
    rw [hb]
    simp only [hc', ite_true]
    refine ⟨by simp, (fromBytes_spec hI _).2.2.2.2.1.trans hb, (st.fromBytes ((st.data r).take st.size)).2, rfl,
      fun i hi => ?_⟩
    unfold St.fromBytes at hi
    split at hi
    · simp at hi
    · simp at hi; omega
  · have hrb : readBytes st st.size = ({ st with pos := st.pos + st.size }, r) := by
      unfold readBytes; rw [hb]; exact if_pos ⟨by omega, hp, hl, h0⟩
    have e1 : (if (st.size : Int) < 0 then 0 else (st.size : Int)).toNat = st.size := by split <;> omega
    have hr : read st none = keepRes (readBytes st st.size).1 (readBytes st st.size).2 := by
      unfold read; simp [optSsize, hb, hp, e1]
    rw [hr, hrb]; exact ⟨rfl, rfl⟩
  · have hz : ¬ (st.size > 1 ∧ st.pos = 0 ∧ st.size = (st.data r).length ∧ st.exports = 0) := by omega
    have h0 : ¬ st.size = 0 := by omega
    have hsl : slice (st.data r) st.pos st.size = st.data r := by
      rw [hp, hl]; simp [slice]
    have hfb : st.fromBytes (st.data r) = (st.newObj (st.data r), .heap st.next) := by
      unfold St.fromBytes; rw [if_neg (by omega)]
    have hrb : readBytes st st.size = ({ st.newObj (st.data r) with pos := st.pos + st.size }, .heap st.next) := by
      unfold readBytes; rw [hb]; dsimp only; rw [if_neg hz, if_neg h0, hsl, hfb]
    have e1 : (if (st.size : Int) < 0 then 0 else (st.size : Int)).toNat = st.size := by split <;> omega
    have hr : read st none = keepRes (readBytes st st.size).1 (readBytes st st.size).2 := by
      unfold read; simp [optSsize, hb, hp, e1]
    rw [hr, hrb]
    refine ⟨?_, _, rfl, fun i hi => by cases hi; omega⟩
    simp only [keepRes, St.data_pos, St.newObj_data_new]

/-! ### Live views -/

theorem liveCount_append_none (vs : List (Option View)) : liveCount (vs ++ [none]) = liveCount vs := by
  simp [liveCount, List.countP_append]

theorem take_set_lt : ∀ (l : List Nat) (n i x : Nat), (l.set i x).take n = (l.take n).set i x
  | [], _, _, _ => by simp
  | _ :: _, 0, _, _ => by simp
  | _ :: _, _ + 1, 0, _ => by simp
  | y :: ys, n + 1, i + 1, x => by simp [take_set_lt ys n i x]

/-- The unshare before an export succeeds below the allocation bound, and `self->buf`
then starts with the contents; it is a singleton only for an empty stream. -/
theorem exportPrep_ok {st : St} {r : Ref} (hI : Inv st) (hb : st.buf = some r) (hm : st.size < memLimit) :
    ∃ st1 r1, exportPrep st r = .ok st1 ∧ st1.buf = some r1 ∧
      (st1.data r1).take st.size = (st.data r).take st.size ∧ st1.size = st.size ∧ st1.views = st.views ∧
      (∀ d, r1 = .single d → st.size = 0) := by
  unfold exportPrep
  split
  · rename_i hc
    unfold unshare
    rw [hb]
    simp only [ssize_ok hm, ite_false]
    by_cases hz : st.size = 0
    · simp only [hz, ite_true]
      refine ⟨_, _, rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> simp
    · simp only [hz, ite_false, allocBytes_ok hm]
      refine ⟨_, _, rfl, rfl, ?_, rfl, rfl, fun d h => by cases h⟩
      simp only [St.data_buf, St.newObj_data_new, Nat.sub_self, List.replicate_zero, List.append_nil,
        List.take_take, Nat.min_self]
  · rename_i hc
    refine ⟨st, r, rfl, hb, rfl, rfl, rfl, fun d hd => ?_⟩
    subst hd
    have hex : st.exports ≠ 0 := by
      intro h0; apply hc; exact ⟨h0, rfl⟩
    obtain ⟨w, hw⟩ := liveCount_pos (Nat.pos_of_ne_zero hex)
    obtain ⟨hwb, hwl, _, hws⟩ := hI.views w hw
    rw [hb] at hwb
    have hwt : w.target = .single d := by simpa using hwb.symm
    rw [← hwl]; exact hws d hwt

/-- `getbuffer()` returns a live read-write view of the contents (Doc/library/io.rst:741-749:
"Return a readable and writable view over the contents of the buffer without copying them.
Also, mutating the view will transparently update the contents of the buffer"): it adds
one export, it reads the contents, a byte stored through it at any index below the size
is in the next `getvalue()`, an index past the end raises `IndexError`; while it lives every
write, truncate and close raises `BufferError` ("As long as the view exists, the BytesIO
object cannot be resized or closed", :752-753; C refuses in-place writes too); releasing
it gives the export back. Hypotheses: reachable state, size within the allocation and
below the allocation bound. -/
def BytesIOGetbufferLive : Prop := ∀ (st : St) (r : Ref), Inv st → st.buf = some r →
    st.size ≤ (st.data r).length → st.size < memLimit →
  (getbuffer st).2 = .ok .none ∧ (getbuffer st).1.exports = st.exports + 1 ∧
  (viewBytes (getbuffer st).1 st.views.length).2 = .ok (.bytes ((st.data r).take st.size)) ∧
  (∀ i x, i < st.size → x < 256 →
    (viewSet (getbuffer st).1 st.views.length i x).2 = .ok .none ∧
    (getvalue (viewSet (getbuffer st).1 st.views.length i x).1).2 =
      .ok (.bytes (((st.data r).take st.size).set i x))) ∧
  (∀ i x, st.size ≤ i →
    (viewSet (getbuffer st).1 st.views.length i x).2 = .error (.indexError "index out of bounds on dimension 1")) ∧
  (∀ b, (write (getbuffer st).1 b).2 = .error bufferError) ∧
  (∀ n, (truncate (getbuffer st).1 n).2 = .error bufferError) ∧
  (step (getbuffer st).1 .close).2 = .error bufferError ∧
  (release (getbuffer st).1 st.views.length).1.exports = st.exports

theorem bytesIOGetbufferLive_proven : BytesIOGetbufferLive := by
  intro st r hI hb hle hm
  obtain ⟨st1, r1, e, hb1, hd, hsz, hv, hsg⟩ := exportPrep_ok hI hb hm
  have hg : getbuffer st = ({ st1 with views := st1.views ++ [some ⟨r1, st1.size⟩] }, .ok .none) := by
    unfold getbuffer; rw [hb]; simp only [e, hb1]
  have hk : st.views.length = st1.views.length := by rw [hv]
  have hex : liveCount (st1.views ++ [some ⟨r1, st1.size⟩]) = st.exports + 1 := by
    rw [liveCount_append, hv]; rfl
  have hpos : 0 < liveCount (st1.views ++ [some ⟨r1, st1.size⟩]) := by rw [hex]; omega
  rw [hg]
  refine ⟨rfl, hex, ?_, fun i x hi hx => ?_, fun i x hi => ?_, fun b => ?_, fun n => ?_, ?_, ?_⟩
  · simp only [viewBytes, hk, getElem?_append_last, St.data_views]
    rw [hsz, hd]
  · have hr1 : ∃ j, r1 = .heap j := by
      cases r1 with
      | single d => have := hsg d rfl; omega
      | heap j => exact ⟨j, rfl⟩
    obtain ⟨j, rfl⟩ := hr1
    have hi' : i < st1.size := by omega
    have hvs : viewSet { st1 with views := st1.views ++ [some (View.mk (.heap j) st1.size)] } st1.views.length i x =
        (({ st1 with views := st1.views ++ [some (View.mk (.heap j) st1.size)] } : St).setData (.heap j)
          ((st1.data (.heap j)).set i x), .ok .none) := by
      simp only [viewSet, getElem?_append_last, hi', hx, ite_true, St.data_views]
    rw [hk, hvs]
    refine ⟨rfl, ?_⟩
    unfold getvalue
    simp only [St.setData_buf, hb1]
    rw [if_pos (Or.inr (by simp only [St.exports, St.setData_views]; exact hpos))]
    simp only [St.setData_size, St.setData_data_self, take_set_lt]
    rw [hsz, hd]
  · have hi' : ¬ i < st1.size := by omega
    simp only [viewSet, hk, getElem?_append_last, hi', ite_false]
  · unfold write
    simp only [hb1, St.exports, gt_iff_lt, hpos, ite_true]
  · unfold truncate
    simp only [hb1, Option.isNone_some, Bool.false_eq_true, ite_false, St.exports, gt_iff_lt, hpos, ite_true]
  · simp only [step, St.exports, gt_iff_lt, hpos, ite_true]
  · rw [hk]
    simp only [release, getElem?_append_last, set_append_last, St.exports, liveCount_append_none]
    rw [hv]

/-! ### The cached hash -/

/-- `ob_shash` of `r` is unset or the hash of its contents now. -/
def St.hashOk (st : St) : Ref → Bool
  | .single _ => true
  | .heap i =>
    match (st.heap i).hash with
    | none => true
    | some d => decide (d = (st.heap i).data)

/-- Every `bytes` object the program holds hashes as its contents: for every initial
value, operation sequence and kept object `x`, `hash(x) == hash(bytes(bytearray(x)))`,
so `x in {x_copy}` holds (`bytes` are hashable because they are immutable; a `set` or
`dict` relies on it). -/
def BytesIOHashConsistent : Prop := ∀ (init : List Nat) (keep : Bool) (ops : List SOp),
  ∀ r ∈ (runS init keep ops).1.held, (runS init keep ops).1.hashOk r = true

/-- `b = BytesIO(); b.write(b'abcd'); hash(b.getvalue()); b.seek(0); b.write(b'efgh');
v = b.getvalue()`: the first `getvalue()` sizes the buffer to 4 bytes and returns it, the
program hashes and drops it, the second write sees a uniquely referenced buffer that fits
and copies into it in place (bytesio.c:258-269, :286), and the second `getvalue()`
returns the same object with the hash of `b'abcd'` still cached: `v == b'efgh'` but
`v not in {b'efgh'}` (gh-160181; main adds `HASHED_BUF` to `SHARED_BUF`). -/
theorem bytesIOHashConsistent_refuted : ¬BytesIOHashConsistent := by
  intro h
  have := h [] false [.write [97, 98, 99, 100], .getvalue, .hash 0, .drop 0, .seek 0 0,
    .write [101, 102, 103, 104], .getvalue] (.heap 1) (by decide +kernel)
  revert this
  decide +kernel

/-- The same run, as the program sees it: `hash(v) == hash(bytes(bytearray(v)))` is
`False` for the final `v`. -/
theorem bytesIOStaleHash_trace :
    (runS [] false [.write [97, 98, 99, 100], .getvalue, .hash 0, .drop 0, .seek 0 0,
      .write [101, 102, 103, 104], .getvalue, .hash 0]).2 =
    [.ok (.int 4), .ok (.bytes [97, 98, 99, 100]), .ok (.bool true), .ok .none, .ok (.int 0),
     .ok (.int 4), .ok (.bytes [101, 102, 103, 104]), .ok (.bool false)] := by
  decide +kernel

end PyLean.PyIO.Share
