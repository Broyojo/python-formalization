import PyLean.BytesObj.Bytes.Heap
import PyLean.BytesObj.Bytes.ByteArrayProps3

/-!
Lemmas on the heap model: while a C function holds an export of `self`, nothing a callback does
changes the size, the storage or `ob_start` (`Ok`), so a pointer taken at the start reads the live
contents (`read_live`).
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-- The layout of `b` is that of `a`, and the storage is the same object. -/
def Same (a b : H) : Prop :=
  b.gen = a.gen ∧ b.ba.offset = a.ba.offset ∧ b.ba.data.length = a.ba.data.length ∧ b.ba.alloc = a.ba.alloc

/-- More exports than views held by Python code: the C code holds one. -/
def Pinned (h : H) : Prop := h.kept < h.ba.exports

def Ok (a b : H) : Prop := Same a b ∧ Pinned b

theorem Ok.refl (h : H) (hp : Pinned h) : Ok h h := ⟨⟨rfl, rfl, rfl, rfl⟩, hp⟩

theorem Same.trans {a b c : H} (h1 : Same a b) (h2 : Same b c) : Same a c := by
  obtain ⟨g1, o1, l1, a1⟩ := h1
  obtain ⟨g2, o2, l2, a2⟩ := h2
  exact ⟨g2.trans g1, o2.trans o1, l2.trans l1, a2.trans a1⟩

theorem moved_self (b : BA) : b.moved b = false := by
  simp [BA.moved]

theorem put_self (h : H) : h.put h.ba = h := by
  simp [H.put, moved_self]

theorem put_data (h : H) (d : List Int) (hl : d.length = h.ba.data.length) :
    h.put { h.ba with data := d } = { h with ba := { h.ba with data := d } } := by
  have : h.ba.moved { h.ba with data := d } = false := by
    simp [BA.moved, BA.size, hl]
  simp [H.put, this]

/-! ## Each statement keeps a pinned object as it is -/

theorem canResize_pinned (b : BA) (hp : 0 < b.exports) : ∃ e, canResize b = .error e := by
  simp [canResize, hp]

theorem baResize_pinned (b r : BA) (n : Int) (hp : 0 < b.exports) (h : baResize b n = .ok r) :
    n = b.size ∧ r = b := by
  unfold baResize at h
  by_cases h0 : n < 0
  · simp [h0, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · by_cases h1 : n = b.size
    · subst h1
      simp [h0, bind, Except.bind, pure, Except.pure] at h
      exact ⟨rfl, h.symm⟩
    · simp [h0, h1, bind, Except.bind, canResize, hp, throw, throwThe, MonadExceptOf.throw] at h

theorem baResizeLeft_pinned (b : BA) (n : Int) (hp : 0 < b.exports) : baResizeLeft b n = b := by
  unfold baResizeLeft
  simp [hp]

theorem baResizeMethod_pinned (b r : BA) (n : Int) (hp : 0 < b.exports) (h : baResizeMethod b n = .ok r) :
    r = b := by
  unfold baResizeMethod at h
  cases ha : Sequences.asSsize n with
  | error e => simp [ha, bind, Except.bind] at h
  | ok n' =>
    simp only [ha, bind, Except.bind] at h
    cases hr : baResize b n' with
    | error e => simp [hr] at h
    | ok r' =>
      obtain ⟨hn, e⟩ := baResize_pinned b r' n' hp hr
      rw [hr] at h
      rw [e, hn] at h
      simp [pure, Except.pure] at h
      exact h.symm

theorem baCopyIn_nil (b : BA) (lo : Int) : baCopyIn b lo [] = b := by
  simp [baCopyIn]

theorem setsliceLinear_nil_pinned (b r : BA) (lo hi : Int) (hp : 0 < b.exports)
    (h : baSetsliceLinear b lo hi [] = .ok r) : r = b := by
  unfold baSetsliceLinear at h
  simp only [List.length_nil, Int.ofNat_zero] at h
  split at h
  · simp [canResize, hp] at h
  · split at h
    · rename_i hg
      unfold baGrow at h
      simp only [bind, Except.bind] at h
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · cases hr : baResize b (b.size + (0 - (hi - lo))) with
        | error e =>
          simp only [List.length_nil, Int.ofNat_zero, Int.add_zero, Int.sub_zero] at h
          rw [hr] at h
          simp at h
        | ok r' =>
          obtain ⟨hn, _⟩ := baResize_pinned b r' _ hp hr
          omega
    · simp only [Except.ok.injEq] at h
      rw [← h, baCopyIn_nil]

theorem assSlice_front_pinned (b r : BA) (k : Int) (hp : 0 < b.exports)
    (h : baAssSlice b ⟨none, some k, none⟩ none = .ok r) : r = b := by
  unfold baAssSlice at h
  simp only [RangeSlice.sliceUnpack, bind, Except.bind, pure, Except.pure, assValue] at h
  exact setsliceLinear_nil_pinned b r _ _ hp h

theorem baAssIndex_int_shape (b r : BA) (i v : Int) (h : baAssIndex b i (some (.int v)) = .ok r) :
    ∃ k x, r = { b with data := b.data.set k x } := by
  unfold baAssIndex at h
  cases hs : Sequences.subIndex i with
  | error e => simp [hs, bind, Except.bind] at h
  | ok i' =>
    cases hg : getByteValue (.int v) with
    | error e => simp [hs, hg, bind, Except.bind, Functor.map, Except.map] at h
    | ok w =>
      simp only [hs, hg, bind, Except.bind, Functor.map, Except.map] at h
      repeat' split at h
      all_goals first
        | (simp [throw, throwThe, MonadExceptOf.throw] at h; done)
        | (simp only [pure, Except.pure, Except.ok.injEq] at h; exact ⟨_, _, h.symm⟩)

theorem act_ok (h0 h : H) (a : Act) (hk : Ok h0 h) : Ok h0 (Act.run h a) := by
  obtain ⟨hs, hp⟩ := hk
  have hp' : 0 < h.ba.exports := by unfold Pinned at hp; omega
  cases a with
  | set i v =>
    simp only [Act.run]
    split
    · rename_i r hr
      obtain ⟨k, x, e⟩ := baAssIndex_int_shape _ _ _ _ hr
      subst e
      rw [put_data _ _ (List.length_set ..)]
      refine ⟨Same.trans hs ⟨rfl, rfl, List.length_set .., rfl⟩, hp⟩
    · exact ⟨hs, hp⟩
  | resize n =>
    simp only [Act.run]
    split
    · rename_i r hr
      rw [baResizeMethod_pinned _ _ _ hp' hr, put_self]
      exact ⟨hs, hp⟩
    · rw [baResizeLeft_pinned _ _ hp', put_self]
      exact ⟨hs, hp⟩
  | delFront k =>
    simp only [Act.run]
    split
    · rename_i r hr
      rw [assSlice_front_pinned _ _ _ hp' hr, put_self]
      exact ⟨hs, hp⟩
    · exact ⟨hs, hp⟩
  | grab =>
    refine ⟨?_, ?_⟩
    · obtain ⟨g, o, l, al⟩ := hs
      exact ⟨g, o, l, al⟩
    · simp only [Pinned, Act.run, baGetBuffer] at hp ⊢
      omega
  | drop =>
    simp only [Act.run]
    split
    · exact ⟨hs, hp⟩
    · refine ⟨?_, ?_⟩
      · obtain ⟨g, o, l, al⟩ := hs
        exact ⟨g, o, l, al⟩
      · simp only [Pinned, baReleaseBuffer] at hp ⊢
        omega

theorem runActs_ok (h0 h : H) (acts : List Act) (hk : Ok h0 h) : Ok h0 (runActs h acts) := by
  induction acts generalizing h with
  | nil => exact hk
  | cons a rest ih =>
    simp only [runActs, List.foldl_cons]
    exact ih _ (act_ok h0 h a hk)

/-- A pointer taken in `h0` reads the live contents of every `Ok` state. -/
theorem read_same (h0 h : H) (hs : Same h0 h) : h.read h0.ptr 0 h0.ba.size = .ok h.ba.seq := by
  obtain ⟨g, o, l, _⟩ := hs
  unfold H.read H.ptr
  simp only [BA.size] at *
  by_cases hn : (h0.ba.data.length : Int) = 0
  · have h00 : h.ba.data.length = 0 := by omega
    have : h.ba.data = [] := List.eq_nil_of_length_eq_zero h00
    simp [hn, BA.seq, this]
  · have hc : (0 ≤ h0.ba.offset + 0 - h0.ba.offset ∧ 0 ≤ (h0.ba.data.length : Int) ∧
        h0.ba.offset + 0 - h0.ba.offset + h0.ba.data.length ≤ h.ba.data.length) := by omega
    have hj : (h0.ba.offset + 0 - h0.ba.offset).toNat = 0 := by omega
    simp only [hn, ↓reduceIte, g, o, ne_eq, not_true_eq_false, hc, and_self, hj, List.drop_zero]
    rw [← l]
    simp [BA.seq]

theorem read_live (h0 h : H) (hk : Ok h0 h) : h.read h0.ptr 0 h0.ba.size = .ok h.ba.seq :=
  read_same h0 h hk.1

theorem readE_live (h0 h : H) (hk : Ok h0 h) : readE h0.ptr 0 h0.ba.size h = curSeq h := by
  simp [readE, curSeq, read_live h0 h hk]

end PyLean.BytesObj.Bytes

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-! ## The views Python code holds are exports -/

def Inv (h : H) : Prop := h.kept ≤ h.ba.exports

theorem baResize_exports (b r : BA) (n : Int) (h : baResize b n = .ok r) : r.exports = b.exports := by
  unfold baResize at h
  by_cases h0 : n < 0
  · simp [h0, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · by_cases h1 : n = b.size
    · subst h1
      simp [h0, bind, Except.bind, pure, Except.pure] at h
      rw [← h]
    · simp only [h0, h1, ↓reduceIte, bind, Except.bind, pure, Except.pure] at h
      repeat' split at h
      all_goals first
        | (simp [throw, throwThe, MonadExceptOf.throw] at h; done)
        | (simp only [Except.ok.injEq, reduceCtorEq] at h; try (rw [← h]))
        | skip
      all_goals simp_all

theorem baResizeLeft_exports (b : BA) (n : Int) : (baResizeLeft b n).exports = b.exports := by
  unfold baResizeLeft
  repeat' split
  all_goals rfl

theorem baResizeMethod_exports (b r : BA) (n : Int) (h : baResizeMethod b n = .ok r) : r.exports = b.exports := by
  unfold baResizeMethod at h
  cases ha : Sequences.asSsize n with
  | error e => simp [ha, bind, Except.bind] at h
  | ok n' =>
    simp only [ha, bind, Except.bind] at h
    cases hr : baResize b n' with
    | error e => simp [hr] at h
    | ok r' =>
      have e := baResize_exports b r' n' hr
      rw [hr] at h
      simp only at h
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        rw [← h]
        exact e
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        rw [← h]
        exact e

theorem baCopyIn_exports (b : BA) (lo : Int) (xs : List Int) : (baCopyIn b lo xs).exports = b.exports := rfl

theorem baResizeNoSize_exports (b r : BA) (n : Int) (h : baResizeNoSize b n = .ok r) : r.exports = b.exports := by
  unfold baResizeNoSize at h
  simp only [bind, Except.bind] at h
  repeat' split at h
  all_goals simp_all [pure, Except.pure]
  all_goals (rw [← h])

theorem shrinkStart_exports (b r : BA) (g : Int) (xs : List Int) (h : baShrinkStart b g xs = .ok r) :
    r.exports = b.exports := by
  unfold baShrinkStart at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i r1 h1
    simp only [pure, Except.pure, Except.ok.injEq] at h
    rw [← h, baCopyIn_exports, baResizeNoSize_exports _ _ _ h1]

theorem shrinkMove_exports (b r : BA) (lo hi g : Int) (xs : List Int) (h : baShrinkMove b lo hi g xs = .ok r) :
    r.exports = b.exports := by
  unfold baShrinkMove at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i s0 hs
    have e0 : s0.exports = b.exports := by
      unfold setsliceShrinkMove at hs
      simp only [bind, Except.bind] at hs
      split at hs
      · simp at hs
      · simp only [pure, Except.pure, Except.ok.injEq] at hs
        rw [← hs]
    split at h
    · simp at h
    · rename_i r1 h1
      simp only [pure, Except.pure, Except.ok.injEq] at h
      rw [← h, baCopyIn_exports, ← e0]
      exact baResize_exports _ _ _ h1

theorem grow_exports (b r : BA) (lo hi g : Int) (xs : List Int) (h : baGrow b lo hi g xs = .ok r) :
    r.exports = b.exports := by
  unfold baGrow at h
  simp only [bind, Except.bind] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · split at h
    · simp at h
    · rename_i r1 h1
      split at h
      · simp at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        rw [← h, baCopyIn_exports]
        show r1.exports = b.exports
        exact baResize_exports _ _ _ h1

theorem setsliceLinear_exports (b r : BA) (lo hi : Int) (xs : List Int)
    (h : baSetsliceLinear b lo hi xs = .ok r) : r.exports = b.exports := by
  unfold baSetsliceLinear at h
  simp only at h
  by_cases hg : (xs.length : Int) - (hi - lo) < 0
  · simp only [hg, ↓reduceIte] at h
    split at h
    · simp at h
    · split at h
      · exact shrinkStart_exports _ _ _ _ h
      · exact shrinkMove_exports _ _ _ _ _ _ h
  · simp only [hg, ↓reduceIte] at h
    by_cases hg2 : (xs.length : Int) - (hi - lo) > 0
    · simp only [hg2, ↓reduceIte] at h
      exact grow_exports _ _ _ _ _ _ h
    · simp only [hg2, ↓reduceIte, Except.ok.injEq] at h
      rw [← h]
      rfl

theorem assSlice_front_exports (b r : BA) (k : Int) (h : baAssSlice b ⟨none, some k, none⟩ none = .ok r) :
    r.exports = b.exports := by
  unfold baAssSlice at h
  simp only [RangeSlice.sliceUnpack, bind, Except.bind, pure, Except.pure, assValue] at h
  exact setsliceLinear_exports _ _ _ _ _ h

theorem put_exports (h : H) (b : BA) : (h.put b).ba.exports = b.exports := rfl

theorem put_kept (h : H) (b : BA) : (h.put b).kept = h.kept := rfl

theorem act_inv (h : H) (a : Act) (hi : Inv h) : Inv (Act.run h a) := by
  unfold Inv at *
  cases a with
  | set i v =>
    simp only [Act.run]
    split
    · rename_i r hr
      obtain ⟨k, x, e⟩ := baAssIndex_int_shape _ _ _ _ hr
      rw [put_exports, put_kept, e]
      exact hi
    · exact hi
  | resize n =>
    simp only [Act.run]
    split
    · rename_i r hr
      rw [put_exports, put_kept, baResizeMethod_exports _ _ _ hr]
      exact hi
    · rw [put_exports, put_kept, baResizeLeft_exports]
      exact hi
  | delFront k =>
    simp only [Act.run]
    split
    · rename_i r hr
      rw [put_exports, put_kept, assSlice_front_exports _ _ _ hr]
      exact hi
    · exact hi
  | grab => simp only [Act.run, baGetBuffer]; omega
  | drop =>
    simp only [Act.run]
    split
    · exact hi
    · simp only [baReleaseBuffer]; omega

theorem runActs_inv (h : H) (acts : List Act) (hi : Inv h) : Inv (runActs h acts) := by
  induction acts generalizing h with
  | nil => exact hi
  | cons a rest ih =>
    simp only [runActs, List.foldl_cons]
    exact ih _ (act_inv h a hi)

end PyLean.BytesObj.Bytes

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-! ## Computations that keep an invariant -/

def Keeps {α : Type} (P : H → Prop) (x : E α) : Prop := ∀ h, P h → P (x h).2

theorem keeps_pure {α : Type} (P : H → Prop) (a : α) : Keeps P (pure a : E α) := fun _ hh => hh

theorem keeps_throw {α : Type} (P : H → Prop) (e : PyExc) : Keeps P (throw e : E α) := fun _ hh => hh

theorem keeps_lift {α : Type} (P : H → Prop) (p : Py α) : Keeps P (E.lift p) := fun _ hh => hh

theorem keeps_bind {α β : Type} (P : H → Prop) (x : E α) (f : α → E β) (hx : Keeps P x)
    (hf : ∀ a, Keeps P (f a)) : Keeps P (x >>= f) := by
  intro h hh
  simp only [E.bind_app]
  have := hx h hh
  rcases hxh : x h with ⟨r, h'⟩
  rw [hxh] at this
  cases r with
  | ok a => exact hf a h' this
  | error e => exact this

theorem keeps_runCb_inv {α : Type} (acts : List Act) (res : Py α) : Keeps Inv (runCb acts res) :=
  fun h hh => runActs_inv h acts hh

theorem keeps_runCb_ok {α : Type} (h0 : H) (acts : List Act) (res : Py α) : Keeps (Ok h0) (runCb acts res) :=
  fun h hh => runActs_ok h0 h acts hh

/-- What every argument conversion keeps, given what callbacks keep. -/
structure Good (P : H → Prop) : Prop where
  cb : ∀ (acts : List Act), Keeps P (runCb acts (.ok ()))
  cbAny : ∀ {α : Type} (acts : List Act) (res : Py α), Keeps P (runCb acts res)

theorem good_inv : Good Inv := ⟨fun acts => keeps_runCb_inv acts _, fun acts res => keeps_runCb_inv acts res⟩

theorem good_ok (h0 : H) : Good (Ok h0) :=
  ⟨fun acts => keeps_runCb_ok h0 acts _, fun acts res => keeps_runCb_ok h0 acts res⟩

theorem keeps_indexE (P : H → Prop) (g : Good P) (a : Arg) : Keeps P (indexE a) := by
  cases a with
  | obj o =>
    simp only [indexE]
    split
    · exact keeps_lift P _
    · exact keeps_throw P _
  | idx acts res => exact g.cbAny acts res
  | _ => exact keeps_throw P _

theorem keeps_asSsizeE (P : H → Prop) (g : Good P) (exc : Option (String → PyExc)) (a : Arg) :
    Keeps P (asSsizeE exc a) := by
  unfold asSsizeE
  apply keeps_bind P _ _ (keeps_indexE P g a)
  intro v
  cases exc with
  | none => exact keeps_pure P _
  | some mk =>
    simp only
    split
    · exact keeps_pure P _
    · exact keeps_throw P _

theorem keeps_clinicSsizeE (P : H → Prop) (g : Good P) (a : Arg) : Keeps P (clinicSsizeE a) := by
  unfold clinicSsizeE
  exact keeps_bind P _ _ (keeps_indexE P g a) (fun _ => keeps_lift P _)

theorem keeps_sliceIndexE (P : H → Prop) (g : Good P) (a : Option Arg) : Keeps P (sliceIndexE a) := by
  cases a with
  | none => exact keeps_pure P _
  | some a =>
    simp only [sliceIndexE]
    split
    · exact keeps_pure P _
    · split
      · intro h hh
        simp only [Functor.map]
        exact keeps_bind P _ _ (keeps_asSsizeE P g none a) (fun _ => keeps_pure P _) h hh
      · exact keeps_throw P _

theorem keeps_parse (P : H → Prop) (g : Good P) (sub : Arg) : Keeps P (parseFindsByteE sub) := by
  unfold parseFindsByteE
  split
  · exact keeps_pure P _
  · split
    · exact keeps_throw P _
    · apply keeps_bind P _ _ (keeps_asSsizeE P g none sub)
      intro v
      split
      · exact keeps_throw P _
      · exact keeps_pure P _

/-- Taking a buffer keeps `Ok`: a view of `self` is one more export. -/
theorem getBuf_ok (h0 : H) (a : Arg) : Keeps (Ok h0) (getBufE a) := by
  intro h hh
  cases a with
  | obj o =>
    unfold getBufE
    dsimp only
    cases o.buffer? <;> exact hh
  | buf acts res rel =>
    unfold getBufE
    dsimp only
    exact keeps_bind _ _ _ (keeps_runCb_ok h0 acts res) (fun _ => keeps_pure _ _) h hh
  | slen _ _ s => exact hh
  | me =>
    obtain ⟨⟨g, o, l, al⟩, hp⟩ := hh
    unfold getBufE
    dsimp only
    refine ⟨⟨g, o, l, al⟩, ?_⟩
    simp only [Pinned, baGetBuffer] at hp ⊢
    omega
  | idx _ _ => exact hh
  | it _ _ _ => exact hh

end PyLean.BytesObj.Bytes

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-! ## The search methods read the live object -/

theorem findInternal_live (h0 h : H) (hk : Ok h0 h) (sub : Arg) (st en : Int) (fwd : Bool) :
    findInternalE cRead h0.ptr h0.ba.size sub st en fwd h =
      findInternalE liveRead h0.ptr h0.ba.size sub st en fwd h := by
  unfold findInternalE
  have hp := keeps_parse (Ok h0) (good_ok h0) sub h hk
  rcases hx : parseFindsByteE sub h with ⟨r, h1⟩
  rw [hx] at hp
  simp only [E.bind_app, hx]
  cases r with
  | error e => rfl
  | ok fs =>
    cases fs with
    | byte v =>
      simp only at hp
      simp only [cRead, liveRead, E.bind_app, readE_live h0 h1 hp]
    | obj a =>
      simp only [E.bind_app]
      have hb := getBuf_ok h0 a h1 hp
      rcases hy : getBufE a h1 with ⟨r2, h2⟩
      rw [hy] at hb
      cases r2 with
      | error e => rfl
      | ok b =>
        simp only at hb
        simp only [cRead, liveRead, E.bind_app, readE_live h0 h2 hb]

theorem count_live (h0 h : H) (hk : Ok h0 h) (sub : Arg) (st en : Int) :
    countE cRead h0.ptr h0.ba.size sub st en h = countE liveRead h0.ptr h0.ba.size sub st en h := by
  unfold countE
  have hp := keeps_parse (Ok h0) (good_ok h0) sub h hk
  rcases hx : parseFindsByteE sub h with ⟨r, h1⟩
  rw [hx] at hp
  simp only [E.bind_app, hx]
  cases r with
  | error e => rfl
  | ok fs =>
    cases fs with
    | byte v =>
      simp only at hp
      simp only [cRead, liveRead, E.bind_app, readE_live h0 h1 hp]
    | obj a =>
      simp only [E.bind_app]
      have hb := getBuf_ok h0 a h1 hp
      rcases hy : getBufE a h1 with ⟨r2, h2⟩
      rw [hy] at hb
      cases r2 with
      | error e => rfl
      | ok b =>
        simp only at hb
        simp only [cRead, liveRead, E.bind_app, readE_live h0 h2 hb]

/-- A reader that leaves the heap alone. -/
def Pure (rd : Ptr → Int → E Seq) : Prop := ∀ p n h, (rd p n h).2 = h

theorem pure_cRead : Pure cRead := fun _ _ _ => rfl

theorem pure_liveRead : Pure liveRead := fun _ _ _ => rfl

theorem release_get (b : BA) : baReleaseBuffer (baGetBuffer b) = b := by
  simp [baReleaseBuffer, baGetBuffer]

/-- `tailmatchE` keeps `Ok`: the buffer it takes it releases. -/
theorem tailmatch_ok (h0 : H) (rd : Ptr → Int → E Seq) (hrd : Pure rd) (p : Ptr)
    (len : Int) (a : Arg) (st en : Int) (fwd : Bool) : Keeps (Ok h0) (tailmatchE rd p len a st en fwd) := by
  intro h hh
  unfold tailmatchE
  simp only [E.bind_app]
  cases a with
  | me =>
    unfold getBufE
    dsimp only
    rcases hx : rd p len { h with ba := baGetBuffer h.ba } with ⟨r, h2⟩
    have e2 := hrd p len { h with ba := baGetBuffer h.ba }
    rw [hx] at e2
    simp only at e2
    subst e2
    cases r with
    | error e => exact getBuf_ok h0 .me h hh
    | ok s =>
      simp only [Buf.read, readE, E.bind_app]
      cases hz : H.read { h with ba := baGetBuffer h.ba } h.ptr 0 h.ba.size with
      | error e => exact getBuf_ok h0 .me h hh
      | ok t =>
        simp only [exportsDown, E.modify_app, pure, E.pure, E.bind_app, release_get]
        exact hh
  | obj o =>
    unfold getBufE
    dsimp only
    cases hb : o.buffer? with
    | none => exact hh
    | some t =>
      dsimp only [E.bind_app, pure, E.pure]
      rcases hx : rd p len h with ⟨r, h2⟩
      have e2 := hrd p len h
      rw [hx] at e2
      simp only at e2
      subst e2
      cases r with
      | error e => exact hh
      | ok s => simp [Buf.read, noRel, pure, E.pure]; exact hh
  | buf acts res rel =>
    unfold getBufE
    dsimp only
    simp only [E.bind_app, runCb]
    have h1 := runActs_ok h0 h acts hh
    cases res with
    | error e => exact h1
    | ok t =>
      dsimp only [pure, E.pure]
      rcases hx : rd p len (runActs h acts) with ⟨r, h2⟩
      have e2 := hrd p len (runActs h acts)
      rw [hx] at e2
      simp only at e2
      subst e2
      cases r with
      | error e => exact h1
      | ok s =>
        simp only [Buf.read, pure, E.pure, E.bind_app, runCb]
        exact runActs_ok h0 _ rel h1
  | slen _ _ t =>
    unfold getBufE
    dsimp only [E.bind_app, pure, E.pure]
    rcases hx : rd p len h with ⟨r, h2⟩
    have e2 := hrd p len h
    rw [hx] at e2
    simp only at e2
    subst e2
    cases r with
    | error e => exact hh
    | ok s => simp [Buf.read, noRel, pure, E.pure]; exact hh
  | idx _ _ => exact hh
  | it _ _ _ => exact hh

end PyLean.BytesObj.Bytes

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

theorem tailmatch_live (h0 h : H) (hk : Ok h0 h) (a : Arg) (st en : Int) (fwd : Bool) :
    tailmatchE cRead h0.ptr h0.ba.size a st en fwd h = tailmatchE liveRead h0.ptr h0.ba.size a st en fwd h := by
  unfold tailmatchE
  simp only [E.bind_app]
  have hb := getBuf_ok h0 a h hk
  rcases hy : getBufE a h with ⟨r2, h2⟩
  rw [hy] at hb
  simp only at hb
  cases r2 with
  | error e => rfl
  | ok b => simp only [cRead, liveRead, E.bind_app, readE_live h0 h2 hb]

theorem tailLoop_live (h0 : H) (st en : Int) (fwd : Bool) (items : List Arg) :
    ∀ h, Ok h0 h → tailLoopE cRead h0.ptr h0.ba.size st en fwd items h =
      tailLoopE liveRead h0.ptr h0.ba.size st en fwd items h := by
  induction items with
  | nil => intro h _; rfl
  | cons item rest ih =>
    intro h hk
    simp only [tailLoopE, E.bind_app]
    rw [tailmatch_live h0 h hk item st en fwd]
    have hk2 := tailmatch_ok h0 liveRead pure_liveRead h0.ptr h0.ba.size item st en fwd h hk
    rcases hx : tailmatchE liveRead h0.ptr h0.ba.size item st en fwd h with ⟨r, h2⟩
    rw [hx] at hk2
    simp only at hk2
    cases r with
    | error e => rfl
    | ok t =>
      cases t
      · exact ih h2 hk2
      · rfl

theorem contains_live (h0 h : H) (hk : Ok h0 h) (arg : Arg) :
    (do
      match ← E.attempt (asSsizeE none arg) with
      | .error _ =>
        let b ← getBufE arg
        let s ← cRead h0.ptr h0.ba.size
        let t ← b.read
        let r := decide (stringlibFind s t 0 ≥ 0)
        b.rel
        return r
      | .ok ival =>
        if ival < 0 ∨ ival ≥ 256 then throw (.valueError "byte must be in range(0, 256)")
        let s ← cRead h0.ptr h0.ba.size
        return s.contains ival.toNat : E Bool) h =
    (do
      match ← E.attempt (asSsizeE none arg) with
      | .error _ =>
        let b ← getBufE arg
        let s ← liveRead h0.ptr h0.ba.size
        let t ← b.read
        let r := decide (stringlibFind s t 0 ≥ 0)
        b.rel
        return r
      | .ok ival =>
        if ival < 0 ∨ ival ≥ 256 then throw (.valueError "byte must be in range(0, 256)")
        let s ← liveRead h0.ptr h0.ba.size
        return s.contains ival.toNat : E Bool) h := by
  simp only [E.bind_app, E.attempt_app]
  have ha := keeps_asSsizeE (Ok h0) (good_ok h0) none arg h hk
  rcases hx : asSsizeE none arg h with ⟨r, h1⟩
  rw [hx] at ha
  simp only at ha
  simp only
  cases r with
  | error e =>
    simp only [E.bind_app]
    have hb := getBuf_ok h0 arg h1 ha
    rcases hy : getBufE arg h1 with ⟨r2, h2⟩
    rw [hy] at hb
    simp only at hb
    cases r2 with
    | error e => rfl
    | ok b => simp only [cRead, liveRead, E.bind_app, readE_live h0 h2 hb]
  | ok v =>
    simp only
    split
    · rfl
    · simp only [cRead, liveRead, E.bind_app, readE_live h0 h1 ha]

theorem withBuffer_live {α : Type} (op1 op2 : Ptr → Int → E α) (h : H) (hi : Inv h)
    (hop : ∀ h0, Pinned h0 → op1 h0.ptr h0.ba.size h0 = op2 h0.ptr h0.ba.size h0) :
    withBufferE op1 h = withBufferE op2 h := by
  unfold withBufferE
  have hp : Pinned { h with ba := baGetBuffer h.ba } := by
    unfold Inv at hi
    simp only [Pinned, baGetBuffer]
    omega
  have := hop { h with ba := baGetBuffer h.ba } hp
  simp only [H.ptr, baGetBuffer, BA.size] at this ⊢
  rw [this]

/-- The search methods of `bytearray` run with `ob_exports` raised, so every callback of the
argument (`__index__`, `__buffer__`, `__release_buffer__`, the `__index__` of `start` and `end`)
leaves the size and the storage alone: reading through the pointer taken at the start is
reading the object as it is when the search runs. For every heap whose views are exports (the
type invariant `Inv`) and every argument. -/
def SearchReadsLive : Prop :=
  ∀ (h : H), Inv h → ∀ (sub : Arg) (start «end» : Option Arg) (forward : Bool) (fname : String)
    (affix : AffixArg),
    baFindE cRead sub start «end» forward h = baFindE liveRead sub start «end» forward h ∧
    baIndexE cRead sub start «end» forward h = baIndexE liveRead sub start «end» forward h ∧
    baCountE cRead sub start «end» h = baCountE liveRead sub start «end» h ∧
    baTailmatchE cRead fname affix start «end» forward h = baTailmatchE liveRead fname affix start «end» forward h ∧
    baContainsE cRead sub h = baContainsE liveRead sub h

theorem bounds_inv (start «end» : Option Arg) (h : H) (hi : Inv h) {β : Type}
    (k : Option Int → Option Int → E β) (k' : Option Int → Option Int → E β)
    (hk : ∀ a b h', Inv h' → k a b h' = k' a b h') :
    (do let st ← sliceIndexE start; let en ← sliceIndexE «end»; k st en) h =
      (do let st ← sliceIndexE start; let en ← sliceIndexE «end»; k' st en) h := by
  simp only [E.bind_app]
  have h1 := keeps_sliceIndexE Inv good_inv start h hi
  rcases hx : sliceIndexE start h with ⟨r, h1'⟩
  rw [hx] at h1
  cases r with
  | error e => rfl
  | ok st =>
    simp only
    have h2 := keeps_sliceIndexE Inv good_inv «end» h1' h1
    rcases hy : sliceIndexE «end» h1' with ⟨r2, h2'⟩
    rw [hy] at h2
    cases r2 with
    | error e => rfl
    | ok en => exact hk st en h2' h2

theorem searchReadsLive_proven : SearchReadsLive := by
  intro h hi sub start «end» forward fname affix
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold baFindE
    apply bounds_inv start «end» h hi
    intro a b h' hi'
    apply withBuffer_live _ _ h' hi'
    intro h0 hp
    exact findInternal_live h0 h0 (Ok.refl h0 hp) sub _ _ forward
  · unfold baIndexE
    apply bounds_inv start «end» h hi
    intro a b h' hi'
    apply withBuffer_live _ _ h' hi'
    intro h0 hp
    simp only [E.bind_app]
    rw [findInternal_live h0 h0 (Ok.refl h0 hp) sub _ _ forward]
  · unfold baCountE
    apply bounds_inv start «end» h hi
    intro a b h' hi'
    apply withBuffer_live _ _ h' hi'
    intro h0 hp
    exact count_live h0 h0 (Ok.refl h0 hp) sub _ _
  · unfold baTailmatchE
    apply bounds_inv start «end» h hi
    intro a b h' hi'
    apply withBuffer_live _ _ h' hi'
    intro h0 hp
    cases affix with
    | tuple items => exact tailLoop_live h0 _ _ forward items h0 (Ok.refl h0 hp)
    | one x =>
      simp only [E.bind_app, E.attempt_app]
      rw [tailmatch_live h0 h0 (Ok.refl h0 hp) x _ _ forward]
  · unfold baContainsE
    apply withBuffer_live _ _ h hi
    intro h0 hp
    exact contains_live h0 h0 (Ok.refl h0 hp) sub

end PyLean.BytesObj.Bytes

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-! ## With C arguments, the search methods are those of `bytes` -/

theorem clamp_clamp (v : Int) : clampSsize (clampSsize v) = clampSsize v := by
  unfold clampSsize ssizeMin ssizeMax
  omega

theorem parseFindsByte_clamp (v : Int) : parseFindsByte (.byte (clampSsize v)) = parseFindsByte (.byte v) := by
  simp only [parseFindsByte, clamp_clamp]

theorem bytesFindInternal_clamp (s : Seq) (v st en : Int) (fwd : Bool) :
    bytesFindInternal s (.byte (clampSsize v)) st en fwd = bytesFindInternal s (.byte v) st en fwd := by
  unfold bytesFindInternal
  rw [parseFindsByte_clamp]

theorem bytesCount_clamp (s : Seq) (v : Int) (st en : Option Int) :
    bytesCount s (.byte (clampSsize v)) st en = bytesCount s (.byte v) st en := by
  unfold bytesCount
  rw [parseFindsByte_clamp]

theorem bytesFindInternal_range (s : Seq) (v st en : Int) (fwd : Bool) (h : v < 0 ∨ v > 255) :
    bytesFindInternal s (.byte v) st en fwd = .error (.valueError "byte must be in range(0, 256)") := by
  have : clampSsize v < 0 ∨ clampSsize v > 255 := by unfold clampSsize ssizeMin ssizeMax; omega
  simp [bytesFindInternal, parseFindsByte, this, bind, Except.bind]

theorem bytesCount_range (s : Seq) (v : Int) (st en : Option Int) (h : v < 0 ∨ v > 255) :
    bytesCount s (.byte v) st en = .error (.valueError "byte must be in range(0, 256)") := by
  have : clampSsize v < 0 ∨ clampSsize v > 255 := by unfold clampSsize ssizeMin ssizeMax; omega
  simp [bytesCount, parseFindsByte, this, bind, Except.bind]

/-- A bound that is an `int` or absent. -/
def bnd : Option Int → Option Arg
  | none => none
  | some v => some (.obj (.int v))

theorem sliceIndex_bnd (b : Option Int) (h : H) :
    sliceIndexE (bnd b) h = (.ok (b.map clampSsize), h) := by
  cases b with
  | none => rfl
  | some v => rfl

theorem argStart_map (b : Option Int) : (b.map clampSsize).getD 0 = argStart b := by
  cases b <;> rfl

theorem argEnd_map (b : Option Int) : (b.map clampSsize).getD ssizeMax = argEnd b := by
  cases b <;> rfl

theorem withBuffer_seq (h : H) (hi : Inv h) {α : Type} (body : Ptr → Int → E α) (r : Py α)
    (hb : ∀ h1 : H, h1 = { h with ba := baGetBuffer h.ba } → body h1.ptr h1.ba.size h1 = (r, h1)) :
    withBufferE body h = (r, h) := by
  unfold withBufferE
  have := hb _ rfl
  simp only [H.ptr, baGetBuffer, BA.size] at this ⊢
  rw [this]
  simp [baReleaseBuffer]

theorem getBuf_obj (o : Obj) (t : Seq) (hb : o.buffer? = some t) (h : H) :
    getBufE (.obj o) h = (.ok ⟨.bytes t, noRel⟩, h) := by
  unfold getBufE
  dsimp only
  rw [hb]
  rfl

theorem parse_obj_buf (o : Obj) (t : Seq) (hb : o.buffer? = some t) (h : H) :
    parseFindsByteE (.obj o) h = (.ok (.obj (.obj o)), h) := by
  unfold parseFindsByteE
  simp [Arg.bufferCheck, hb]

theorem parse_obj_noindex (o : Obj) (hb : o.buffer? = none) (hx : o.index? = none) (h : H) :
    parseFindsByteE (.obj o) h =
      (.error (.typeError s!"argument should be integer or bytes-like object, not '{o.typeName}'"), h) := by
  unfold parseFindsByteE
  simp [Arg.bufferCheck, Arg.indexCheck, hb, hx, Arg.typeName]

theorem parse_obj_index_err (o : Obj) (e : PyExc) (hb : o.buffer? = none) (hx : o.index? = some (.error e))
    (h : H) : parseFindsByteE (.obj o) h = (.error e, h) := by
  unfold parseFindsByteE
  simp [Arg.bufferCheck, Arg.indexCheck, hb, hx, asSsizeE, indexE]

theorem parse_obj_index_ok (o : Obj) (v : Int) (hb : o.buffer? = none) (hx : o.index? = some (.ok v))
    (h : H) : parseFindsByteE (.obj o) h =
      (if clampSsize v < 0 ∨ clampSsize v > 255 then .error (.valueError "byte must be in range(0, 256)")
       else .ok (.byte (clampSsize v)), h) := by
  unfold parseFindsByteE
  simp only [Arg.bufferCheck, Arg.indexCheck, hb, hx, Option.isSome_none, Option.isSome_some,
    Bool.false_eq_true, ↓reduceIte, Bool.not_true, E.bind_app, asSsizeE, indexE, E.lift_app, E.pure_app]
  split <;> rfl

/-- The search body on a C argument: `parse_args_finds_byte` of `bytes`, then the search on the
contents. -/
theorem seq_getBuffer (b : BA) : (baGetBuffer b).seq = b.seq := rfl

theorem argStart_idem (x : Option Int) : argStart (some (argStart x)) = argStart x := by
  cases x <;> simp [argStart, clamp_clamp] <;> rfl

theorem argEnd_idem (x : Option Int) : argEnd (some (argEnd x)) = argEnd x := by
  cases x <;> simp [argEnd, clamp_clamp] <;> unfold clampSsize ssizeMin ssizeMax <;> omega

theorem bytesCount_args (s : Seq) (b : BSub) (st en : Option Int) :
    bytesCount s b (some (argStart st)) (some (argEnd en)) = bytesCount s b st en := by
  unfold bytesCount
  rw [argStart_idem, argEnd_idem]

theorem ok_bind {α β : Type} (x : α) (f : α → Py β) : (Except.ok x >>= f : Py β) = f x := rfl

theorem findInternal_obj (h1 : H) (hp : Pinned h1) (o : Obj) (st en : Int) (fwd : Bool) :
    findInternalE cRead h1.ptr h1.ba.size (.obj o) st en fwd h1 =
      ((do let b ← parseFindsByteObj o; bytesFindInternal h1.ba.seq b st en fwd), h1) := by
  have rl := readE_live h1 h1 (Ok.refl _ hp)
  unfold findInternalE parseFindsByteObj
  cases hb : o.buffer? with
  | some t =>
    simp only [E.bind_app, parse_obj_buf o t hb, getBuf_obj o t hb, cRead, rl, curSeq, Buf.read,
      E.pure_app, noRel, E.lift_app, ok_bind]
  | none =>
    cases hx : o.index? with
    | none => simp only [E.bind_app, parse_obj_noindex o hb hx]; rfl
    | some r =>
      cases r with
      | error e => simp only [E.bind_app, parse_obj_index_err o e hb hx]; rfl
      | ok v =>
        simp only [E.bind_app, parse_obj_index_ok o v hb hx]
        by_cases hr : clampSsize v < 0 ∨ clampSsize v > 255
        · simp only [hr, ↓reduceIte, ok_bind]
          rw [bytesFindInternal_range _ _ _ _ _ (by unfold clampSsize ssizeMin ssizeMax at hr; omega)]
        · simp only [hr, ↓reduceIte, cRead, E.bind_app, rl, curSeq, E.lift_app, bytesFindInternal_clamp,
            ok_bind]

theorem count_obj (h1 : H) (hp : Pinned h1) (o : Obj) (st en : Int) :
    countE cRead h1.ptr h1.ba.size (.obj o) st en h1 =
      ((do let b ← parseFindsByteObj o; bytesCount h1.ba.seq b (some st) (some en)), h1) := by
  have rl := readE_live h1 h1 (Ok.refl _ hp)
  unfold countE parseFindsByteObj
  cases hb : o.buffer? with
  | some t =>
    simp only [E.bind_app, parse_obj_buf o t hb, getBuf_obj o t hb, cRead, rl, curSeq, Buf.read,
      E.pure_app, noRel, E.lift_app, ok_bind]
  | none =>
    cases hx : o.index? with
    | none => simp only [E.bind_app, parse_obj_noindex o hb hx]; rfl
    | some r =>
      cases r with
      | error e => simp only [E.bind_app, parse_obj_index_err o e hb hx]; rfl
      | ok v =>
        simp only [E.bind_app, parse_obj_index_ok o v hb hx]
        by_cases hr : clampSsize v < 0 ∨ clampSsize v > 255
        · simp only [hr, ↓reduceIte, ok_bind]
          rw [bytesCount_range _ _ _ _ (by unfold clampSsize ssizeMin ssizeMax at hr; omega)]
        · simp only [hr, ↓reduceIte, cRead, E.bind_app, rl, curSeq, E.lift_app, bytesCount_clamp,
            ok_bind]

/-- `bytearray.find`, `rfind`, `index`, `rindex` and `count` with an argument and bounds that
run no Python code are the `bytes` methods on the contents, and leave the object as it was. -/
def SearchTwinBytes : Prop :=
  ∀ (h : H), Inv h → ∀ (o : Obj) (st en : Option Int) (forward : Bool),
    baFindE cRead (.obj o) (bnd st) (bnd en) forward h = (bytesFindObj h.ba.seq o st en forward, h) ∧
    baIndexE cRead (.obj o) (bnd st) (bnd en) forward h = (bytesIndexObj h.ba.seq o st en forward, h) ∧
    baCountE cRead (.obj o) (bnd st) (bnd en) h = (bytesCountObj h.ba.seq o st en, h)

theorem searchTwinBytes_proven : SearchTwinBytes := by
  intro h hi o st en forward
  have hp : Pinned { h with ba := baGetBuffer h.ba } := by
    unfold Inv at hi; simp only [Pinned, baGetBuffer]; omega
  refine ⟨?_, ?_, ?_⟩
  · unfold baFindE
    simp only [E.bind_app, sliceIndex_bnd]
    apply withBuffer_seq h hi
    intro h1 e1
    subst e1
    rw [findInternal_obj _ hp, argStart_map, argEnd_map]
    rfl
  · unfold baIndexE
    simp only [E.bind_app, sliceIndex_bnd]
    apply withBuffer_seq h hi
    intro h1 e1
    subst e1
    simp only [E.bind_app]
    rw [findInternal_obj _ hp, argStart_map, argEnd_map]
    simp only [seq_getBuffer]
    unfold bytesIndexObj bytesIndex
    cases parseFindsByteObj o with
    | error e => rfl
    | ok b =>
      simp only [ok_bind]
      cases bytesFindInternal h.ba.seq b (argStart st) (argEnd en) forward with
      | error e => rfl
      | ok r =>
        by_cases hr : r = -1
        · simp [hr, ok_bind, E.throw_app, throw, throwThe, MonadExceptOf.throw, E.bind_app, Except.bind,
            bind]
          rfl
        · simp [hr, ok_bind, E.pure_app, pure, Except.pure]
          rfl
  · unfold baCountE
    simp only [E.bind_app, sliceIndex_bnd]
    apply withBuffer_seq h hi
    intro h1 e1
    subst e1
    rw [count_obj _ hp, argStart_map, argEnd_map]
    simp only [seq_getBuffer]
    unfold bytesCountObj
    cases parseFindsByteObj o with
    | error e => rfl
    | ok b =>
      simp only [ok_bind, bytesCount_args]

end PyLean.BytesObj.Bytes

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-! ## strip copies after the release -/

/-- The bytes `strip` returns are the ones its loops scanned: copying after the argument's
`__release_buffer__` (the C order, :2460-2462) gives what copying before it gives. -/
def StripCopiesScanned : Prop :=
  ∀ (h : H), Inv h → ∀ (arg : Option Arg) (t : StripType),
    (baStripE true arg t h).1 = (baStripE false arg t h).1

/-- `bytearray(b" a ").strip(B())` where `B.__buffer__` gives `b" "` and `B.__release_buffer__`
does `self[1] = 32`: the loops find `a` between the spaces, the copy reads the space written over
it, and the result is `bytearray(b" ")`, which still ends in a byte of the set. -/
def stripHeap : H := { ba := { data := [32, 97, 32], alloc := 3 } }

theorem strip_rewritten :
    (baStripE true (some (.buf [] (.ok [32]) [.set 1 32])) .both stripHeap).1 = .ok [32] ∧
    (baStripE false (some (.buf [] (.ok [32]) [.set 1 32])) .both stripHeap).1 = .ok [97] := by
  constructor <;> rfl

/-- With `self.clear()` in `__release_buffer__` the copy reads the freed storage. -/
theorem strip_freed :
    (baStripE true (some (.buf [] (.ok [32]) [.resize 0])) .both stripHeap).1 = .error uafRead := by
  rfl

theorem stripCopiesScanned_refuted : ¬ StripCopiesScanned := by
  intro hs
  have := hs stripHeap (by unfold Inv; decide) (some (.buf [] (.ok [32]) [.set 1 32])) .both
  rw [strip_rewritten.1, strip_rewritten.2] at this
  exact absurd this (by decide)

/-! ## Without Python code in `__release_buffer__` -/

/-- The argument's `PyBuffer_Release` runs no Python code: `None`, a C object, `self`, a `bytes`
subclass, or a class whose `__release_buffer__` does nothing to `self`. -/
def NoRelCode : Option Arg → Prop
  | some (.buf _ _ rel) => rel = []
  | _ => True

theorem read_slice (h : H) (l r : Nat) (hlr : l ≤ r) (hr : r ≤ h.ba.data.length) :
    h.read h.ptr l (r - l) = .ok ((h.ba.seq.drop l).take (r - l)) := by
  unfold H.read H.ptr
  by_cases hn : ((r : Int) - l) = 0
  · have : r - l = 0 := by omega
    simp [hn, this]
  · have hc : (0 ≤ h.ba.offset + (l : Int) - h.ba.offset ∧ 0 ≤ (r : Int) - l ∧
        h.ba.offset + (l : Int) - h.ba.offset + ((r : Int) - l) ≤ h.ba.size) := by
      simp only [BA.size]; omega
    have hj : (h.ba.offset + (l : Int) - h.ba.offset).toNat = l := by omega
    have hk : ((r : Int) - l).toNat = r - l := by omega
    simp only [hn, ↓reduceIte, ne_eq, not_true_eq_false, hc, and_self, hj, hk, BA.seq, List.map_take,
      List.map_drop]

theorem stripBounds_le (mem : Nat → Bool) (t : StripType) (s : Seq) :
    (stripBounds mem t s).1 ≤ (stripBounds mem t s).2 ∧ (stripBounds mem t s).2 ≤ s.length := by
  unfold stripBounds
  have tw : ∀ l : Seq, (l.takeWhile mem).length + (l.dropWhile mem).length = l.length := by
    intro l
    rw [← List.length_append, List.takeWhile_append_dropWhile]
  have h1 : (s.takeWhile mem).length ≤ s.length := by have := tw s; omega
  have h2 : ∀ i, (((s.drop i).reverse.dropWhile mem).length) ≤ s.length - i := by
    intro i
    have := tw (s.drop i).reverse
    simp only [List.length_reverse, List.length_drop] at this
    omega
  by_cases hr : t = .right
  · subst hr
    simp only [ne_eq, not_true_eq_false, ↓reduceIte, reduceCtorEq, not_false_eq_true]
    have := h2 0
    omega
  · simp only [ne_eq, hr, not_false_eq_true, ↓reduceIte]
    by_cases hl : t = .left
    · subst hl
      simp only [not_true_eq_false, ↓reduceIte]
      omega
    · simp only [hl, not_false_eq_true, ↓reduceIte]
      have := h2 (s.takeWhile mem).length
      omega

theorem stripBounds_read (h : H) (cs : Seq) (t : StripType) :
    let b := stripBounds (fun c => cs.contains c) t h.ba.seq
    h.read h.ptr (b.1 : Int) ((b.2 : Int) - (b.1 : Int)) = .ok (stripWith (fun c => cs.contains c) t h.ba.seq) := by
  intro b
  obtain ⟨hle, hlen⟩ := stripBounds_le (fun c => cs.contains c) t h.ba.seq
  have hl : h.ba.seq.length = h.ba.data.length := by simp [BA.seq]
  have := read_slice h b.1 b.2 hle (by rw [← hl]; exact hlen)
  rw [this, stripWith_bounds]

/-- With no Python code in `__release_buffer__`, `strip` is the strip of the contents as the
argument's `__buffer__` left them: for `None` the six bytes of `bytearray_strip_impl_helper`, for a
C buffer, for `self` (`b.strip(b)`) and for a class whose `__release_buffer__` does nothing, its
bytes. The object is left as `__buffer__` left it, its exports included. -/
def StripNoRelAgrees : Prop :=
  (∀ (h : H) (t : StripType), baStripE true none t h = (.ok (bytearrayStrip h.ba.seq none t), h)) ∧
  (∀ (h : H) (o : Obj) (cs : Seq) (t : StripType), o.buffer? = some cs →
    baStripE true (some (.obj o)) t h = (.ok (bytearrayStrip h.ba.seq (some cs) t), h)) ∧
  (∀ (h : H) (t : StripType),
    baStripE true (some .me) t h = (.ok (bytearrayStrip h.ba.seq (some h.ba.seq) t), h)) ∧
  (∀ (h : H) (acts : List Act) (cs : Seq) (t : StripType),
    baStripE true (some (.buf acts (.ok cs) [])) t h =
      (.ok (bytearrayStrip (runActs h acts).ba.seq (some cs) t), runActs h acts))

theorem readE_self (h : H) : readE h.ptr 0 h.ba.size h = (.ok h.ba.seq, h) := by
  simp [readE, read_same h h ⟨rfl, rfl, rfl, rfl⟩]

theorem E.bind_def {α β : Type} (x : E α) (f : α → E β) (h : H) :
    E.bind x f h = match x h with
      | (.ok a, h') => f a h'
      | (.error e, h') => (.error e, h') := rfl

theorem E.map_app {α β : Type} (f : α → β) (x : E α) (h : H) :
    (f <$> x) h = match x h with
      | (.ok a, h') => (.ok (f a), h')
      | (.error e, h') => (.error e, h') := by
  show E.bind x (fun a => E.pure (f a)) h = _
  simp only [E.bind_def]
  rfl

theorem readE_app (p : Ptr) (i n : Int) (h : H) : readE p i n h = (h.read p i n, h) := rfl

theorem read_self (h : H) : h.read h.ptr 0 h.ba.size = .ok h.ba.seq := read_same h h ⟨rfl, rfl, rfl, rfl⟩

theorem getBuf_me (h : H) :
    getBufE .me h = (.ok ⟨.self h.ptr h.ba.size, exportsDown⟩, { h with ba := baGetBuffer h.ba }) := by
  unfold getBufE
  rfl

theorem getBuf_buf (acts : List Act) (cs : Seq) (rel : List Act) (h : H) :
    getBufE (.buf acts (.ok cs) rel) h = (.ok ⟨.bytes cs, runCb rel (.ok ())⟩, runActs h acts) := by
  unfold getBufE
  rfl

theorem stripNoRelAgrees_proven : StripNoRelAgrees := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h t
    have := stripBounds_read h [9, 10, 13, 12, 11, 32] t
    simp only at this
    simp only [baStripE, E.bind_app, E.pure_app, E.get_app, readE_app, read_self, this, ↓reduceIte,
      bytearrayStrip, Option.getD_none]
  · intro h o cs t hb
    have hnone : (Arg.obj o).isNone = false := by
      cases o <;> simp_all [Arg.isNone, Obj.buffer?]
    have := stripBounds_read h cs t
    simp only at this
    simp only [baStripE, hnone, Bool.false_eq_true, ↓reduceIte, E.bind_app, E.map_app, getBuf_obj o cs hb,
      E.pure_app, E.get_app, readE_app, read_self, Buf.read, noRel, this, bytearrayStrip, Option.getD_some]
  · intro h t
    have hs : Same h { h with ba := baGetBuffer h.ba } := ⟨rfl, rfl, rfl, rfl⟩
    have r1 := read_same h { h with ba := baGetBuffer h.ba } hs
    have := stripBounds_read h h.ba.seq t
    simp only at this
    have e3 : ({ ba := baReleaseBuffer (baGetBuffer h.ba), gen := h.gen, kept := h.kept } : H) = h := by
      rw [release_get]
    simp only [baStripE, Arg.isNone, Bool.false_eq_true, ↓reduceIte, E.bind_app, E.map_app, getBuf_me,
      E.pure_app, E.get_app, readE_app, Buf.read, exportsDown, E.modify_app]
    simp only [show ({ h with ba := baGetBuffer h.ba } : H).ptr = h.ptr from rfl,
      show ({ h with ba := baGetBuffer h.ba } : H).ba.size = h.ba.size from rfl, r1,
      show ({ h with ba := baGetBuffer h.ba } : H).ba.seq = h.ba.seq from rfl, e3, this,
      bytearrayStrip, Option.getD_some]
  · intro h acts cs t
    have := stripBounds_read (runActs h acts) cs t
    simp only at this
    simp only [baStripE, Arg.isNone, Bool.false_eq_true, ↓reduceIte, E.bind_app, E.map_app, getBuf_buf,
      runCb, E.pure_app, E.get_app, readE_app, read_self, Buf.read, List.foldl_nil, this,
      bytearrayStrip, Option.getD_some]
    simp only [runActs, List.foldl_nil] at this ⊢
    rw [this]

end PyLean.BytesObj.Bytes

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-! ## split, hex and comparison read the live object -/

theorem split_body_live (h0 h : H) (hk : Ok h0 h) (sep : Option Arg) (ms : Int) (right : Bool) :
    splitBodyE cRead h0.ptr h0.ba.size sep ms right h = splitBodyE liveRead h0.ptr h0.ba.size sep ms right h := by
  unfold splitBodyE
  cases sep with
  | none => simp only [cRead, liveRead, E.bind_app, readE_live h0 h hk]
  | some a =>
    by_cases hn : a.isNone = true
    · simp only [hn, ↓reduceIte, cRead, liveRead, E.bind_app, readE_live h0 h hk]
    · simp only [hn, Bool.false_eq_true, ↓reduceIte, E.bind_app]
      have hb := getBuf_ok h0 a h hk
      rcases hy : getBufE a h with ⟨r2, h2⟩
      rw [hy] at hb
      simp only at hb
      cases r2 with
      | error e => rfl
      | ok b => simp only [cRead, liveRead, E.bind_app, readE_live h0 h2 hb]

theorem keeps_lengthE (h0 : H) (a : Arg) : Keeps (Ok h0) (lengthE a) := by
  intro h hh
  cases a with
  | slen acts res s =>
    unfold lengthE
    refine keeps_bind _ _ _ (keeps_runCb_ok h0 acts res) (fun v => ?_) h hh
    intro h' hh'
    simp only
    split
    · exact hh'
    · split
      · exact hh'
      · exact hh'
  | obj o => exact hh
  | me => exact hh
  | idx _ _ => exact hh
  | buf _ _ _ => exact hh
  | it _ _ _ => exact hh

theorem keeps_hexSep (h0 : H) (sep : Option Arg) : Keeps (Ok h0) (hexSepE sep) := by
  cases sep with
  | none => exact keeps_pure _ _
  | some a => exact keeps_bind _ _ _ (keeps_lengthE h0 a) (fun _ => keeps_lift _ _)

/-- `bytearray.split`, `rsplit` and `hex`: the separator's callbacks (`__buffer__`, `__len__`)
run with `ob_exports` raised, so the pointer taken before them reads the object as it is when
the C code reads it. For every heap whose views are exports. -/
def SplitReadsLive : Prop :=
  ∀ (h : H), Inv h → ∀ (sep maxsplit : Option Arg) (right : Bool),
    baSplitE cRead sep maxsplit right h = baSplitE liveRead sep maxsplit right h

theorem splitReadsLive_proven : SplitReadsLive := by
  intro h hi sep maxsplit right
  unfold baSplitE
  cases maxsplit with
  | none =>
    simp only [E.bind_app, E.pure_app]
    apply withBuffer_live _ _ h hi
    intro h0 hp
    exact split_body_live h0 h0 (Ok.refl h0 hp) sep _ right
  | some a =>
    simp only [E.bind_app]
    have hk := keeps_clinicSsizeE Inv good_inv a h hi
    rcases hx : clinicSsizeE a h with ⟨r, h1⟩
    rw [hx] at hk
    simp only at hk
    cases r with
    | error e => rfl
    | ok ms =>
      simp only
      apply withBuffer_live _ _ h1 hk
      intro h0 hp
      exact split_body_live h0 h0 (Ok.refl h0 hp) sep ms right

/-- `bytearray.hex`: `argbuf` is read before `ob_exports` is raised, and the separator's
`__len__` (gh-143195) runs after; the hexlify loop reads the live object. -/
def HexReadsLive : Prop :=
  ∀ (h : H), Inv h → ∀ (sep bps : Option Arg),
    baHexE cRead sep bps h = baHexE liveRead sep bps h

theorem hex_body_live (h : H) (hi : Inv h) (sep : Option Arg) (bps : Int) :
    (do
      let h' ← E.get
      let p := h'.ptr
      let arglen := h'.ba.size
      exportsUp
      let r ← E.attempt (do
        let parsed ← hexSepE sep
        let arg ← cRead p arglen
        E.lift (strhexBody arg parsed bps))
      exportsDown
      E.lift r : E Seq) h =
    (do
      let h' ← E.get
      let p := h'.ptr
      let arglen := h'.ba.size
      exportsUp
      let r ← E.attempt (do
        let parsed ← hexSepE sep
        let arg ← liveRead p arglen
        E.lift (strhexBody arg parsed bps))
      exportsDown
      E.lift r : E Seq) h := by
  simp only [E.bind_app, E.get_app, exportsUp, E.modify_app, E.attempt_app]
  have hp : Ok h { h with ba := baGetBuffer h.ba } := by
    refine ⟨⟨rfl, rfl, rfl, rfl⟩, ?_⟩
    unfold Inv at hi; simp only [Pinned, baGetBuffer]; omega
  have hk := keeps_hexSep h sep { h with ba := baGetBuffer h.ba } hp
  rcases hx : hexSepE sep { h with ba := baGetBuffer h.ba } with ⟨r, h1⟩
  rw [hx] at hk
  simp only at hk
  cases r with
  | error e => rfl
  | ok parsed => simp only [cRead, liveRead, readE_live h h1 hk]

theorem hexReadsLive_proven : HexReadsLive := by
  intro h hi sep bps
  unfold baHexE
  cases bps with
  | none =>
    simp only [E.bind_app, E.pure_app]
    exact hex_body_live h hi sep 1
  | some a =>
    simp only [E.bind_app]
    have hk := keeps_clinicSsizeE Inv good_inv a h hi
    rcases hx : clinicSsizeE a h with ⟨r, h1⟩
    rw [hx] at hk
    simp only at hk
    cases r with
    | error e => rfl
    | ok v =>
      simp only
      have := hex_body_live h1 hk sep v
      simp only [E.bind_app] at this
      exact this

/-- `bytearray_richcompare`: the other operand's `__buffer__` runs after `self` is exported, so the
`memcmp` reads `self` as it is then. -/
def RichReadsLive : Prop :=
  ∀ (h : H), Inv h → ∀ (other : Arg) (op : CmpOp), baRichE cRead other op h = baRichE liveRead other op h

theorem richReadsLive_proven : RichReadsLive := by
  intro h hi other op
  unfold baRichE
  by_cases hb : other.bufferCheck = true
  · simp only [hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte, E.bind_app, getBuf_me, E.attempt_app]
    have hp : Ok h { h with ba := baGetBuffer h.ba } := by
      refine ⟨⟨rfl, rfl, rfl, rfl⟩, ?_⟩
      unfold Inv at hi; simp only [Pinned, baGetBuffer]; omega
    have hk := getBuf_ok h other _ hp
    rcases hx : getBufE other { h with ba := baGetBuffer h.ba } with ⟨r, h2⟩
    rw [hx] at hk
    simp only at hk
    cases r with
    | error e => rfl
    | ok vo =>
      simp only
      split
      · rfl
      · simp only [E.bind_app, cRead, liveRead, readE_live h h2 hk]
  · simp only [Bool.not_eq_true] at hb
    simp [hb]

end PyLean.BytesObj.Bytes

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-! ## `b += x` and `b.extend(x)` -/

/-- `b += x` and `b.extend(x)` agree for every bytes-like `x` (`s += t` "extends s with the contents
of t", Doc/library/stdtypes.rst, mutable sequence operations). -/
def IAddIsExtend : Prop :=
  ∀ (h : H), Inv h → ∀ (x : Arg), x.bufferCheck = true → (baIConcatE x h).1 = (baExtendE x h).1

def iaddHeap : H := { ba := { data := [97], alloc := 1 } }

/-- `b = bytearray(b"a"); b += b` raises `BufferError`: `bytearray_iconcat_lock_held` exports `b` as
its own argument and then resizes it. `b.extend(b)` copies first (:697-707) and gives `b"aa"`. -/
theorem iadd_self : (baIConcatE .me iaddHeap).1 = .error (bufferError "Existing exports of data: object cannot be re-sized") ∧
    (baExtendE .me iaddHeap).1 = .ok () ∧ (baExtendE .me iaddHeap).2.ba.data = [97, 97] := by
  refine ⟨rfl, rfl, rfl⟩

theorem iAddIsExtend_refuted : ¬ IAddIsExtend := by
  intro hh
  have := hh iaddHeap (by unfold Inv; decide) .me rfl
  rw [iadd_self.1, iadd_self.2.1] at this
  exact absurd this (by decide)

/-! ## The two ways `bytearray(str, encoding)` installs the encoded bytes -/

/-- `bytearray.__init__(s, encoding)` gives the same object whether the codec's result is uniquely
referenced (it becomes the storage, :1031-1038) or not (it is appended with `bytearray_iconcat`,
:1040): the uniqueness of a `bytes` object is not visible to Python code. -/
def InitPathsAgree : Prop :=
  ∀ (h : H), Inv h → ∀ (cs : Seq) (name : String) (acts : List Act) (enc : Seq),
    let r1 := baInitE (some (.obj (.str cs))) (some (name, .py acts (.ok enc) true)) none h
    let r2 := baInitE (some (.obj (.str cs))) (some (name, .py acts (.ok enc) false)) none h
    r1.1 = r2.1 ∧ r1.2.ba.data = r2.2.ba.data

def initHeap : H := { ba := { data := [120], alloc := 1 } }

/-- A codec that does `self.resize(2)`: the unique result replaces the storage and the two zero
bytes are dropped (and their `bytes` object leaked); the shared result is appended after them. -/
theorem init_steal_drops :
    (baInitE (some (.obj (.str [104, 105]))) (some ("rcodec", .py [.resize 2] (.ok [104, 105]) true)) none
      initHeap).2.ba.data = [104, 105] ∧
    (baInitE (some (.obj (.str [104, 105]))) (some ("rcodec", .py [.resize 2] (.ok [104, 105]) false)) none
      initHeap).2.ba.data = [0, 0, 104, 105] := by
  refine ⟨rfl, rfl⟩

/-- A codec that keeps `memoryview(self)`: the unique result is installed under the export, the
shared one is refused. -/
theorem init_steal_exported :
    (baInitE (some (.obj (.str [104, 105]))) (some ("rcodec", .py [.grab] (.ok [104, 105]) true)) none
      initHeap).1 = .ok () ∧
    (baInitE (some (.obj (.str [104, 105]))) (some ("rcodec", .py [.grab] (.ok [104, 105]) true)) none
      initHeap).2.ba.exports = 1 ∧
    (baInitE (some (.obj (.str [104, 105]))) (some ("rcodec", .py [.grab] (.ok [104, 105]) false)) none
      initHeap).1 = .error (bufferError "Existing exports of data: object cannot be re-sized") := by
  refine ⟨rfl, rfl, rfl⟩

theorem initPathsAgree_refuted : ¬ InitPathsAgree := by
  intro hh
  have := (hh initHeap (by unfold Inv; decide) [104, 105] "rcodec" [.resize 2] [104, 105]).2
  rw [init_steal_drops.1, init_steal_drops.2] at this
  exact absurd this (by decide)

theorem resize_len (b r : BA) (n : Int) (h : baResize b n = .ok r) : (r.data.length : Int) = n := by
  obtain ⟨h0, hc⟩ := baResize_cases b r n h
  rcases hc with ⟨e, hn⟩ | ⟨_, _, hd, _⟩
  · subst e; simp [hn, BA.size]
  · rw [hd]; exact resizedData_length _ _ h0

/-- For a C bytes-like object that is not `self`, `b += x` is `b.extend(x)`: the same result and the
same contents. (Open: the proof has to follow `bytearray_setslice_linear`'s growth branch.) -/
def IAddExtendObj : Prop :=
  ∀ (h : H) (o : Obj) (t : Seq), o.buffer? = some t →
    (baIConcatE (.obj o) h).1 = (baExtendE (.obj o) h).1 ∧
    (baIConcatE (.obj o) h).2.ba.data = (baExtendE (.obj o) h).2.ba.data

end PyLean.BytesObj.Bytes

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-! ## Item access after `__index__` -/

theorem runCb_app {α : Type} (acts : List Act) (res : Py α) (h : H) : runCb acts res h = (res, runActs h acts) := rfl

theorem put_ok (h : H) (f : BA → Py BA) : liftBA f h = match f h.ba with
    | .ok b => (.ok (), h.put b)
    | .error e => (.error e, h) := rfl

/-- `b[k]`, `b[i] = v`, `del b[i]`, `b.append(v)`, `b.insert(i, v)`, `b.remove(v)` and
`b.take_bytes(n)` with an `__index__` that changes `b`: the conversion runs first, and then the
method of the pure model runs on the object as the callback left it, so the index is checked
against the size after the callback (GH-91153). An exception from `__index__` is raised before
any check of the index, with the callback's changes kept. For every heap and every callback, with
values that fit in `Py_ssize_t`. -/
def ItemAfterIndex : Prop :=
  ∀ (h : H) (acts : List Act) (v : Int), ssizeMin ≤ v → v ≤ ssizeMax →
    let h' := runActs h acts
    -- b[k] for k.__index__() = v
    baSubscriptE (.one (.idx acts (.ok v))) h = ((SubRes.byte <$> baGetItem h'.ba v), h') ∧
    -- b[i] = x with x.__index__() = v
    (∀ i : Int, ssizeMin ≤ i → i ≤ ssizeMax →
      baAssSubE (.one (.obj (.int i))) (some (.idx acts (.ok v))) h = liftBA (fun b => baAssIndex b i (some (.int v))) h') ∧
    -- the same through sq_ass_item
    (∀ i : Int, baSetItemE i (some (.idx acts (.ok v))) h = liftBA (fun b => baSetItemRaw b i (some (.int v))) h') ∧
    baAppendE (.idx acts (.ok v)) h = liftBA (fun b => baAppend b (.int v)) h' ∧
    baRemoveE (.idx acts (.ok v)) h = liftBA (fun b => baRemove b (.int v)) h' ∧
    (∀ i : Int, ssizeMin ≤ i → i ≤ ssizeMax →
      baInsertE (.obj (.int i)) (.idx acts (.ok v)) h = liftBA (fun b => baInsert b i (.int v)) h') ∧
    baTakeBytesE (some (.idx acts (.ok v))) h = liftBAR (fun b => baTakeBytes b (.int v)) h' ∧
    -- an exception of the value's __index__ comes before the IndexError of the position
    (∀ (e : PyExc) (i : Int), ssizeMin ≤ i → i ≤ ssizeMax →
      baAssSubE (.one (.obj (.int i))) (some (.idx acts (.error e))) h = (.error e, h'))

theorem getByte_idx (acts : List Act) (v : Int) (h : H) :
    getByteValueE (.idx acts (.ok v)) h =
      ((if v < 0 ∨ v ≥ 256 then .error (.valueError "byte must be in range(0, 256)") else .ok v.toNat),
        runActs h acts) := by
  simp only [getByteValueE, indexE, E.bind_app, runCb_app]
  split <;> rfl

theorem getByteValue_int (v : Int) :
    getByteValue (.int v) = (if v < 0 ∨ v ≥ 256 then .error (.valueError "byte must be in range(0, 256)") else .ok v.toNat) := by
  simp only [getByteValue, Obj.index?]

theorem E.throw_bind {α β : Type} (e : PyExc) (f : α → E β) (h : H) :
    E.bind (throw e : E α) f h = (.error e, h) := rfl

theorem E.get_bind {β : Type} (f : H → E β) (h : H) : E.bind E.get f h = f h h := rfl

theorem E.pure_bind {α β : Type} (a : α) (f : α → E β) (h : H) : E.bind (pure a : E α) f h = f a h := rfl

theorem E.bind_err {α β : Type} (e : PyExc) (f : α → E β) (s : H) :
    E.bind (fun h => ((.error e : Py α), h)) f s = (.error e, s) := rfl

theorem max_byte (v : Int) (hv : ¬(v < 0 ∨ v ≥ 256)) : max v 0 = v := by omega

theorem itemAfterIndex_proven : ItemAfterIndex := by
  intro h acts v h1 h2
  dsimp only
  have hs : Sequences.subIndex v = .ok v := by
    simp only [Sequences.subIndex, Sequences.asSsizeExc, h1, h2, and_self, ↓reduceIte]
  have hr : ssizeMin ≤ v ∧ v ≤ ssizeMax := ⟨h1, h2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [baSubscriptE, Arg.indexCheck, Bool.not_true, Bool.false_eq_true, ↓reduceIte, E.bind_app,
      asSsizeE, indexE, runCb_app, hr, and_self, E.pure_app, curSize, E.get_app]
    unfold baGetItem baGetItemRaw
    simp only [hs, bind, Except.bind]
    split <;> split <;> simp_all [E.throw_bind, E.get_bind, Functor.map, Except.map]
  · intro i hi1 hi2
    have hsi : Sequences.subIndex i = .ok i := by
      simp only [Sequences.subIndex, Sequences.asSsizeExc, hi1, hi2, and_self, ↓reduceIte]
    unfold baAssIndex
    by_cases hv : v < 0 ∨ v ≥ 256
    · simp [baAssSubE, Arg.indexCheck, Obj.index?, asSsizeE, indexE, hi1, hi2, Functor.map, E.bind_def,
        getByte_idx, hv, put_ok, hsi, getByteValue_int, bind, Except.bind, Except.map]
    · have hm := max_byte v hv
      simp [baAssSubE, Arg.indexCheck, Obj.index?, asSsizeE, indexE, hi1, hi2, Functor.map, E.bind_def,
        getByte_idx, hv, put_ok, hsi, getByteValue_int, bind, Except.bind, Except.map, E.pure, curSize, hm,
        Function.comp]
      repeat' split
      all_goals simp_all [E.throw_bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure, put_ok, E.bind_err]
  · intro i
    unfold baSetItemRaw
    by_cases hv : v < 0 ∨ v ≥ 256
    · simp [baSetItemE, Functor.map, E.bind_def, getByte_idx, hv, put_ok, getByteValue_int, bind, Except.bind,
        Except.map]
    · have hm := max_byte v hv
      simp [baSetItemE, Functor.map, E.bind_def, getByte_idx, hv, put_ok, getByteValue_int, bind, Except.bind,
        Except.map, E.pure, curSize, hm, Function.comp]
      repeat' split
      all_goals simp_all [E.throw_bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure, put_ok, E.bind_err]
  · simp only [baAppendE, E.bind_app, getByte_idx]
    unfold baAppend
    simp only [put_ok, getByteValue_int, bind, Except.bind]
    by_cases hv : v < 0 ∨ v ≥ 256
    · simp [hv]
    · have hm := max_byte v hv
      simp [hv, hm, pure, Except.pure, put_ok, E.pure]
  · simp only [baRemoveE, E.bind_app, getByte_idx]
    unfold baRemove
    simp only [put_ok, getByteValue_int, bind, Except.bind]
    by_cases hv : v < 0 ∨ v ≥ 256
    · simp [hv]
    · have hm := max_byte v hv
      simp [hv, hm, pure, Except.pure, put_ok, E.pure]
  · intro i hi1 hi2
    have ha : Sequences.asSsize i = .ok i := by
      simp only [Sequences.asSsize, hi1, hi2, and_self, ↓reduceIte]
    simp only [baInsertE, clinicSsizeE, indexE, Obj.index?, E.bind_app, E.lift_app, ha, getByte_idx]
    unfold baInsert
    simp only [put_ok, ha, getByteValue_int, bind, Except.bind]
    by_cases hv : v < 0 ∨ v ≥ 256
    · simp [hv]
    · have hm := max_byte v hv
      simp [hv, hm, pure, Except.pure, put_ok, E.pure]
  · simp only [baTakeBytesE, Arg.isNone, Bool.false_eq_true, ↓reduceIte, Arg.indexCheck, E.bind_app,
      asSsizeE, indexE, runCb_app, hr, and_self, E.pure_app, curSize, liftBAR]
    unfold baTakeBytes
    simp only [Obj.index?, takeCount, hr, and_self, ↓reduceIte, bind, Except.bind, pure, Except.pure]
  · intro e i hi1 hi2
    simp only [baAssSubE, Arg.indexCheck, Obj.index?, Option.isSome_some, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, E.bind_app, asSsizeE, indexE, E.lift_app, hi1, hi2, and_self, E.pure_app, Functor.map,
      E.bind_def, getByteValueE, runCb_app]

end PyLean.BytesObj.Bytes

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-! ## partition reads `self` after both callbacks of the separator -/

theorem baFromStringAndSize_ok (n : Int) (h0 : 0 ≤ n) (h1 : n < 2 ^ 46) :
    ∃ b, baFromStringAndSize none n = .ok b := by
  unfold baFromStringAndSize
  have hn : ¬ n < 0 := by omega
  have hc : bytesSizeCheck n = .ok () := by
    unfold bytesSizeCheck mallocFails bytesObjectSize
    unfold ssizeMax
    split
    · rfl
    · have e1 : ¬ (9223372036854775774 < n) := by omega
      have e2 : ¬ (140737488355328 ≤ 33 + n) := by omega
      simp only [decide_eq_true_eq] at *
      simp [e1, e2]
  simp only [hn, ↓reduceIte, hc]
  split <;> exact ⟨_, rfl⟩

/-- `bytearray.partition(sep)` and `rpartition(sep)` copy the separator first
(`_PyByteArray_FromBufferObject`: its `__buffer__`, then its `__release_buffer__`) and read `self`
only then: the result is `stringlib_partition` of the contents as both callbacks left them, and of
the separator's bytes. For a C bytes-like separator that is `bytes.partition` on the contents. For
every heap, with a separator below 2^46 bytes (`PyByteArray_FromStringAndSize` of its length cannot
fail). -/
def PartitionAfterSep : Prop :=
  (∀ (h : H) (acts rel : List Act) (t : Seq) (right : Bool), t.length < 2 ^ 46 →
    baPartitionE (.buf acts (.ok t) rel) right h =
      ((if right then stringlibRPartition else stringlibPartition) (runActs (runActs h acts) rel).ba.seq t,
        runActs (runActs h acts) rel)) ∧
  (∀ (h : H) (o : Obj) (t : Seq), o.buffer? = some t → t.length < 2 ^ 46 →
    baPartitionE (.obj o) false h = (bytesPartition h.ba.seq t, h) ∧
    baPartitionE (.obj o) true h = (bytesRPartition h.ba.seq t, h))

theorem partitionAfterSep_proven : PartitionAfterSep := by
  refine ⟨?_, ?_⟩
  · intro h acts rel t right ht
    obtain ⟨b, hb⟩ := baFromStringAndSize_ok t.length (by omega) (by exact_mod_cast ht)
    simp only [baPartitionE, E.bind_app, getBuf_buf, Buf.len, hb, Buf.read, E.pure_app, runCb_app, curSeq,
      E.lift_app]
  · intro h o t hb ht
    obtain ⟨b, hb2⟩ := baFromStringAndSize_ok t.length (by omega) (by exact_mod_cast ht)
    refine ⟨?_, ?_⟩
    · simp only [baPartitionE, E.bind_app, getBuf_obj o t hb, Buf.len, hb2, Buf.read, E.pure_app, noRel,
        curSeq, E.lift_app, bytesPartition, Bool.false_eq_true, ↓reduceIte]
    · simp only [baPartitionE, E.bind_app, getBuf_obj o t hb, Buf.len, hb2, Buf.read, E.pure_app, noRel,
        curSeq, E.lift_app, bytesRPartition, ↓reduceIte]

end PyLean.BytesObj.Bytes

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-- `bytearray.translate(table)` reads `self` after the table's `__buffer__` and before its
`__release_buffer__`: with a table class of 256 bytes and no `delete`, the result is the fast loop
over the contents as `__buffer__` left them, and the object is left as both callbacks left it. With
a C table and C `delete` it is the pure `bytearray.translate` on the contents. For every heap below
2^46 bytes (`PyByteArray_FromStringAndSize` of the result cannot fail). -/
def TranslateAfterArgs : Prop :=
  (∀ (h : H) (acts rel : List Act) (t : Seq), t.length = 256 → (runActs h acts).ba.data.length < 2 ^ 46 →
    baTranslateE (.buf acts (.ok t) rel) none h =
      (.ok (translateFast (runActs h acts).ba.seq t), runActs (runActs h acts) rel)) ∧
  (∀ (h : H) (t : Seq), t.length = 256 → h.ba.data.length < 2 ^ 46 →
    baTranslateE (.obj (.bytes t)) none h = (bytearrayTranslate h.ba.seq (.bytes t) none, h)) ∧
  (∀ (h : H) (d : Seq), h.ba.data.length < 2 ^ 46 →
    baTranslateE (.obj .none) (some (.obj (.bytes d))) h =
      (bytearrayTranslate h.ba.seq .none (some (.bytes d)), h))

theorem translateAfterArgs_proven : TranslateAfterArgs := by
  refine ⟨?_, ?_, ?_⟩
  · intro h acts rel t ht hs
    obtain ⟨b, hb⟩ := baFromStringAndSize_ok (runActs h acts).ba.size (by simp [BA.size]) (by
      simp only [BA.size]; exact_mod_cast hs)
    have h256 : ¬ ((t.length : Int) ≠ 256) := by simp [ht]
    simp only [baTranslateE, Arg.isNone, Bool.false_eq_true, ↓reduceIte, E.bind_app, getBuf_buf, Buf.len,
      h256, E.pure_app, curSize, hb, curSeq, Buf.read, runCb_app, Functor.map, E.bind_def]
    rfl
  · intro h t ht hs
    obtain ⟨b, hb⟩ := baFromStringAndSize_ok h.ba.size (by simp [BA.size]) (by simp only [BA.size]; exact_mod_cast hs)
    have h256 : ¬ ((t.length : Int) ≠ 256) := by simp [ht]
    have h256' : ¬ (t.length ≠ 256) := by simp [ht]
    simp only [baTranslateE, Arg.isNone, Bool.false_eq_true, ↓reduceIte, E.bind_app,
      getBuf_obj (.bytes t) t rfl, Buf.len, h256, E.pure_app, curSize, hb, curSeq, Buf.read, noRel, Functor.map,
      E.bind_def]
    simp only [bytearrayTranslate, getBuffer, Obj.buffer?, h256', ↓reduceIte, bind, Except.bind, pure, Except.pure]
    rfl
  · intro h d hs
    obtain ⟨b, hb⟩ := baFromStringAndSize_ok h.ba.size (by simp [BA.size]) (by simp only [BA.size]; exact_mod_cast hs)
    simp only [baTranslateE, Arg.isNone, ↓reduceIte, E.bind_app, E.attempt_app,
      getBuf_obj (.bytes d) d rfl, E.pure_app, curSize, hb, curSeq, Buf.read, noRel, Functor.map, E.bind_def]
    simp only [bytearrayTranslate, getBuffer, Obj.buffer?, bind, Except.bind, pure, Except.pure]

end PyLean.BytesObj.Bytes

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-! ## The methods that read `self` after their conversions -/

theorem clinic_idx (acts : List Act) (v : Int) (hv : ssizeMin ≤ v ∧ v ≤ ssizeMax) (h : H) :
    clinicSsizeE (.idx acts (.ok v)) h = (.ok v, runActs h acts) := by
  simp [clinicSsizeE, indexE, runCb_app, Sequences.asSsize, hv]

theorem clinic_int (v : Int) (hv : ssizeMin ≤ v ∧ v ≤ ssizeMax) (h : H) :
    clinicSsizeE (.obj (.int v)) h = (.ok v, h) := by
  simp [clinicSsizeE, indexE, Obj.index?, Sequences.asSsize, hv]

/-- `center`, `ljust`, `rjust`, `zfill`, `replace`, `expandtabs` and `splitlines` of `bytearray`
raise no export: the arguments' callbacks (`__index__` of `width`, `count` and `tabsize`,
`__buffer__` of `old` and `new`) run first, may resize the object (nothing refuses), and the result
is the `bytes` method on the contents as they left them; `replace` releases its buffers after the
copy, so `__release_buffer__` acts on the object afterwards. For every heap and every callback, with
converted values in `Py_ssize_t`. Scope: callbacks act on `self` only, and a Python `__buffer__`
returns `memoryview(bytes(...))`. -/
def ReadAfterArgs : Prop :=
  (∀ (h : H) (k : PadKind) (acts : List Act) (w : Int) (fill : Nat), ssizeMin ≤ w → w ≤ ssizeMax →
    baPadE k (.idx acts (.ok w)) fill h = (padOp k (runActs h acts).ba.seq w fill, runActs h acts)) ∧
  (∀ (h : H) (w : Int) (fill : Nat), ssizeMin ≤ w → w ≤ ssizeMax →
    baPadE .center (.obj (.int w)) fill h = (bytesCenter h.ba.seq w fill, h) ∧
    baPadE .ljust (.obj (.int w)) fill h = (bytesLjust h.ba.seq w fill, h) ∧
    baPadE .rjust (.obj (.int w)) fill h = (bytesRjust h.ba.seq w fill, h) ∧
    baPadE .zfill (.obj (.int w)) fill h = (bytesZfill h.ba.seq w, h)) ∧
  (∀ (h : H) (a1 r1 a2 r2 : List Act) (o n : Seq),
    baReplaceE (.buf a1 (.ok o) r1) (.buf a2 (.ok n) r2) none h =
      (bytesReplace (runActs (runActs h a1) a2).ba.seq o n (-1),
        runActs (runActs (runActs (runActs h a1) a2) r1) r2)) ∧
  (∀ (h : H) (acts : List Act) (t : Int),
    baExpandtabsE (some (.idx acts (.ok t))) h = (bytesExpandtabs (runActs h acts).ba.seq t, runActs h acts)) ∧
  (∀ (h : H) (keepends : Bool), baSplitlinesE keepends h = (.ok (bytesSplitlines h.ba.seq keepends), h))

theorem readAfterArgs_proven : ReadAfterArgs := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h k acts w fill h1 h2
    simp [baPadE, E.bind_app, clinic_idx acts w ⟨h1, h2⟩, curSeq]
  · intro h w fill h1 h2
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [baPadE, E.bind_app, clinic_int w ⟨h1, h2⟩, curSeq, padOp]
  · intro h a1 r1 a2 r2 o n
    simp [baReplaceE, E.bind_app, E.attempt_app, getBuf_buf, curSeq, Buf.read, runCb_app, E.pure_app]
  · intro h acts t
    simp [baExpandtabsE, E.bind_app, indexE, runCb_app, curSeq]
  · intro h keepends
    rfl

end PyLean.BytesObj.Bytes

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-- `bytearray.remove(c)` (the body after `_getbytevalue`, :2401-2421) removes the first occurrence,
as `list.remove` does, and raises `ValueError("value not found in bytearray")` when there is none;
with exports it refuses a removal with `BufferError`. For every object below 2^45 bytes. -/
def RemoveSpec : Prop :=
  ∀ (b : BA) (c : Nat), c < 256 → b.size < 2 ^ 45 →
    (b.data.findIdx? (· == (c : Int)) = none →
      baRemove b (.int c) = .error (.valueError "value not found in bytearray")) ∧
    (∀ i, b.data.findIdx? (· == (c : Int)) = some i → b.exports = 0 →
      ∃ r, baRemove b (.int c) = .ok r ∧ r.data = b.data.eraseIdx i) ∧
    (∀ i, b.data.findIdx? (· == (c : Int)) = some i → 0 < b.exports →
      baRemove b (.int c) = .error (bufferError "Existing exports of data: object cannot be re-sized"))

theorem removeSpec_proven : RemoveSpec := by
  intro b c hc hs
  have hg := getByte_ok c hc
  refine ⟨?_, ?_, ?_⟩
  · intro hn
    simp [baRemove, hg, hn, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · intro i hi hE
    have hlt : i < b.data.length := (List.findIdx?_eq_some_iff_findIdx_eq.mp hi).1
    obtain ⟨r, hr⟩ := resize_small b (b.size - 1) (by simp only [BA.size]; omega) hE (by omega)
    refine ⟨{ r with data := b.data.eraseIdx i }, ?_, rfl⟩
    simp [baRemove, hg, hi, bind, Except.bind, canResize, hE, hr, pure, Except.pure]
  · intro i hi hE
    simp [baRemove, hg, hi, bind, Except.bind, canResize, hE]

end PyLean.BytesObj.Bytes

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-! ## With C arguments, `in`, `startswith`, `split`, `hex` and comparison are those of `bytes` -/

theorem getBuf_obj_none (o : Obj) (hb : o.buffer? = none) (h : H) :
    getBufE (.obj o) h = (.error (notBytesLike o), h) := by
  unfold getBufE
  dsimp only
  rw [hb]
  rfl

theorem pinned_up (h : H) (hi : Inv h) : Pinned { h with ba := baGetBuffer h.ba } := by
  unfold Inv at hi; simp only [Pinned, baGetBuffer]; omega

theorem contains_twin (h : H) (hi : Inv h) (o : Obj) :
    baContainsE cRead (.obj o) h = (bytesContains h.ba.seq o, h) := by
  have rl := readE_live { h with ba := baGetBuffer h.ba } { h with ba := baGetBuffer h.ba } (Ok.refl _ (pinned_up h hi))
  unfold baContainsE
  apply withBuffer_seq h hi
  intro h1 e1
  subst e1
  have hv : ∀ (r : Py Bool), (match getBuffer o with
      | .error e => .error e
      | .ok b => .ok (decide (stringlibFind h.ba.seq b 0 ≥ 0)) : Py Bool) = r →
      (do
        let b ← getBufE (.obj o)
        let s ← cRead { h with ba := baGetBuffer h.ba }.ptr { h with ba := baGetBuffer h.ba }.ba.size
        let t ← b.read
        let r := decide (stringlibFind s t 0 ≥ 0)
        b.rel
        return r : E Bool) { h with ba := baGetBuffer h.ba } = (r, { h with ba := baGetBuffer h.ba }) := by
    intro r hr
    cases hb : o.buffer? with
    | none =>
      simp only [getBuffer, hb] at hr
      rw [← hr]
      simp only [E.bind_app, getBuf_obj_none o hb]
    | some t =>
      simp only [getBuffer, hb] at hr
      rw [← hr]
      simp only [E.bind_app, getBuf_obj o t hb, cRead, rl, curSeq, Buf.read, E.pure_app, noRel, seq_getBuffer]
  unfold bytesContains
  simp only [E.bind_app, E.attempt_app]
  cases hx : o.index? with
  | none =>
    simp only [asSsizeE, indexE, hx, E.bind_app, E.throw_app]
    exact hv _ rfl
  | some r =>
    cases r with
    | error e =>
      simp only [asSsizeE, indexE, hx, E.bind_app, E.lift_app]
      exact hv _ rfl
    | ok v =>
      simp only [asSsizeE, indexE, hx, E.bind_app, E.lift_app, E.pure_app]
      split
      · rfl
      · simp only [cRead, E.bind_app, rl, curSeq, seq_getBuffer, E.pure_app]

theorem split_twin (h : H) (hi : Inv h) (o : Obj) (t : Seq) (m : Int) (right : Bool)
    (hb : o.buffer? = some t) (h1 : ssizeMin ≤ m) (h2 : m ≤ ssizeMax) :
    baSplitE cRead (some (.obj o)) (some (.obj (.int m))) right h =
      ((if right then bytesRSplit else bytesSplit) h.ba.seq (some t) m, h) := by
  have rl := readE_live { h with ba := baGetBuffer h.ba } { h with ba := baGetBuffer h.ba } (Ok.refl _ (pinned_up h hi))
  unfold baSplitE
  simp only [E.bind_app, clinic_int m ⟨h1, h2⟩]
  apply withBuffer_seq h hi
  intro h1' e1
  subst e1
  have hn : (Arg.obj o).isNone = false := by cases o <;> simp_all [Arg.isNone, Obj.buffer?]
  simp only [splitBodyE, hn, Bool.false_eq_true, ↓reduceIte, E.bind_app, getBuf_obj o t hb, cRead, rl, curSeq,
    Buf.read, E.pure_app, noRel, seq_getBuffer, E.lift_app]

theorem split_twin_none (h : H) (hi : Inv h) (m : Int) (right : Bool) (h1 : ssizeMin ≤ m) (h2 : m ≤ ssizeMax) :
    baSplitE cRead none (some (.obj (.int m))) right h =
      ((if right then bytesRSplit else bytesSplit) h.ba.seq none m, h) := by
  have rl := readE_live { h with ba := baGetBuffer h.ba } { h with ba := baGetBuffer h.ba } (Ok.refl _ (pinned_up h hi))
  unfold baSplitE
  simp only [E.bind_app, clinic_int m ⟨h1, h2⟩]
  apply withBuffer_seq h hi
  intro h1' e1
  subst e1
  simp only [splitBodyE, E.bind_app, cRead, rl, curSeq, seq_getBuffer, E.lift_app]

theorem strhexImpl_none (s : Seq) (bps : Int) : strhexImpl s none bps false = strhexBody s none bps := rfl

theorem hex_twin (h : H) (bps : Int) (h1 : ssizeMin ≤ bps) (h2 : bps ≤ ssizeMax) :
    baHexE cRead none (some (.obj (.int bps))) h = (bytesHex h.ba.seq none bps, h) := by
  have hr : ¬ (bps < ssizeMin ∨ bps > ssizeMax) := by omega
  have rs := read_same h { h with ba := baGetBuffer h.ba } ⟨rfl, rfl, rfl, rfl⟩
  have e3 : ({ ba := baReleaseBuffer (baGetBuffer h.ba), gen := h.gen, kept := h.kept } : H) = h := by
    rw [release_get]
  simp only [baHexE, E.bind_app, clinic_int bps ⟨h1, h2⟩, E.get_app, exportsUp, E.modify_app, E.attempt_app,
    hexSepE, E.pure_app, cRead, readE_app, rs, E.lift_app, exportsDown, e3, bytesHex, hr, ↓reduceIte,
    strhexImpl_none, seq_getBuffer]

/-- `bytearray_richcompare` against a C object is the comparison of the two byte strings. -/
theorem rich_twin (h : H) (o : Obj) (op : CmpOp) :
    baRichE cRead (.obj o) op h = (.ok (baRichcompare (.bytearray h.ba.seq) o op), h) := by
  unfold baRichE baRichcompare
  cases hb : o.buffer? with
  | none =>
    have hbc : (Arg.obj o).bufferCheck = false := by simp [Arg.bufferCheck, hb]
    simp [hbc, hb]
  | some t =>
    have hbc : (Arg.obj o).bufferCheck = true := by simp [Arg.bufferCheck, hb]
    have rs := read_same h { h with ba := baGetBuffer h.ba } ⟨rfl, rfl, rfl, rfl⟩
    have e3 : ({ ba := baReleaseBuffer (baGetBuffer h.ba), gen := h.gen, kept := h.kept } : H) = h := by
      rw [release_get]
    have hlen : h.ba.size = (h.ba.seq.length : Int) := by simp [BA.size, BA.seq]
    simp only [hbc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, E.bind_app, getBuf_me, E.attempt_app,
      getBuf_obj o t hb, Obj.buffer?, Buf.len]
    by_cases hc : h.ba.size ≠ (t.length : Int) ∧ (op = .eq ∨ op = .ne)
    · have hc' : h.ba.seq.length ≠ t.length ∧ (op = .eq ∨ op = .ne) := by
        refine ⟨?_, hc.2⟩; intro e; apply hc.1; rw [hlen, e]
      simp only [hc, and_self, ↓reduceIte, exportsDown, E.modify_app, E.bind_app, noRel, E.pure_app, e3, hc',
        ne_eq, not_false_eq_true]
    · have hc' : ¬ (h.ba.seq.length ≠ t.length ∧ (op = .eq ∨ op = .ne)) := by
        intro e; apply hc; refine ⟨?_, e.2⟩; intro e2; apply e.1; rw [hlen] at e2; exact_mod_cast e2
      simp only [hc, ↓reduceIte, cRead, readE_app, rs, E.bind_app, Buf.read, E.pure_app, exportsDown,
        E.modify_app, noRel, e3, hc']
      rw [hlen]
      simp only [seq_getBuffer]
      split <;> simp_all [E.pure_app]

theorem tail_twin (h : H) (hi : Inv h) (o : Obj) (t : Seq) (hb : o.buffer? = some t) (fname : String)
    (st en : Option Int) (fwd : Bool) :
    baTailmatchE cRead fname (.one (.obj o)) (bnd st) (bnd en) fwd h =
      (bytesTailmatchObj h.ba.seq fname o (argStart st) (argEnd en) fwd, h) := by
  have rl := readE_live { h with ba := baGetBuffer h.ba } { h with ba := baGetBuffer h.ba } (Ok.refl _ (pinned_up h hi))
  have hpure : bytesTailmatchObj h.ba.seq fname o (argStart st) (argEnd en) fwd =
      .ok (bytesTailmatch h.ba.seq t (argStart st) (argEnd en) fwd) := by
    cases o <;> simp_all [Obj.buffer?, bytesTailmatchObj, tailItem, getBuffer]
  rw [hpure]
  unfold baTailmatchE
  simp only [E.bind_app, sliceIndex_bnd]
  apply withBuffer_seq h hi
  intro h1 e1
  subst e1
  simp only [E.bind_app, E.attempt_app, tailmatchE, getBuf_obj o t hb, cRead, rl, curSeq, Buf.read, E.pure_app,
    noRel, seq_getBuffer, argStart_map, argEnd_map]

/-- With arguments that run no Python code, `in`, `startswith`/`endswith` of one buffer, `split` and
`rsplit`, `hex()` and comparison give what the `bytes` methods give on the contents, and leave the
object as it was. For every heap whose views are exports. -/
def CopyTwinBytes : Prop :=
  ∀ (h : H), Inv h →
    (∀ o : Obj, baContainsE cRead (.obj o) h = (bytesContains h.ba.seq o, h)) ∧
    (∀ (o : Obj) (t : Seq) (fname : String) (st en : Option Int) (fwd : Bool), o.buffer? = some t →
      baTailmatchE cRead fname (.one (.obj o)) (bnd st) (bnd en) fwd h =
        (bytesTailmatchObj h.ba.seq fname o (argStart st) (argEnd en) fwd, h)) ∧
    (∀ (o : Obj) (t : Seq) (m : Int) (right : Bool), o.buffer? = some t → ssizeMin ≤ m → m ≤ ssizeMax →
      baSplitE cRead (some (.obj o)) (some (.obj (.int m))) right h =
        ((if right then bytesRSplit else bytesSplit) h.ba.seq (some t) m, h)) ∧
    (∀ (m : Int) (right : Bool), ssizeMin ≤ m → m ≤ ssizeMax →
      baSplitE cRead none (some (.obj (.int m))) right h =
        ((if right then bytesRSplit else bytesSplit) h.ba.seq none m, h)) ∧
    (∀ (bps : Int), ssizeMin ≤ bps → bps ≤ ssizeMax →
      baHexE cRead none (some (.obj (.int bps))) h = (bytesHex h.ba.seq none bps, h)) ∧
    (∀ (o : Obj) (op : CmpOp), baRichE cRead (.obj o) op h = (.ok (baRichcompare (.bytearray h.ba.seq) o op), h))

theorem copyTwinBytes_proven : CopyTwinBytes := fun h hi =>
  ⟨contains_twin h hi, fun o t fname st en fwd hb => tail_twin h hi o t hb fname st en fwd,
   fun o t m right hb h1 h2 => split_twin h hi o t m right hb h1 h2,
   fun m right h1 h2 => split_twin_none h hi m right h1 h2,
   fun bps h1 h2 => hex_twin h bps h1 h2, fun o op => rich_twin h o op⟩

end PyLean.BytesObj.Bytes


namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-! ## Group 1: the bytearray bodies of the delegating methods -/

theorem fromSize_small (b : BA) (h : b.data.length < 2 ^ 46) : ∃ r, baFromStringAndSize none b.seq.length = .ok r := by
  have : b.seq.length = b.data.length := by simp [BA.seq]
  exact baFromStringAndSize_ok _ (by omega) (by rw [this]; exact_mod_cast h)

/-- The predicates of `bytearray` (`isalnum` ... `isupper`, `isascii`, `istitle`) return the bytes
helper's answer on the contents, and the maps (`lower`, `upper`, `swapcase`, `capitalize`,
`title`) a new bytearray holding the helper's result; neither changes the object. For every heap
below 2^46 bytes. -/
def DelegatesSpec : Prop :=
  ∀ (h : H),
    (∀ p ∈ [bytesIsAlnum, bytesIsAlpha, bytesIsAscii, bytesIsDigit, bytesIsLower, bytesIsSpace, bytesIsTitle,
      bytesIsUpper], baPredE p h = (.ok (p h.ba.seq), h)) ∧
    (h.ba.data.length < 2 ^ 46 → ∀ f ∈ [bytesCapitalize, bytesSwapcase, bytesTitle, bytesUpper, bytesLower],
      baMapE f h = (.ok (f h.ba.seq), h))

theorem delegatesSpec_proven : DelegatesSpec := by
  intro h
  refine ⟨fun p _ => rfl, fun hs f _ => ?_⟩
  obtain ⟨r, hr⟩ := fromSize_small h.ba hs
  simp [baMapE, E.bind_app, curSeq, hr]

/-- `removeprefix`/`removesuffix` of `bytearray` lack the `prefix_len > 0` test of the `bytes` bodies
and agree with them anyway (an empty affix takes both to the copy); with a prefix class the result is
taken from the contents as `__buffer__` left them, and `__release_buffer__` runs after. -/
def AffixSpec : Prop :=
  (∀ s p : Seq, baRemoveprefix s p = bytesRemoveprefix s p ∧ baRemovesuffix s p = bytesRemovesuffix s p) ∧
  (∀ (h : H) (acts rel : List Act) (p : Seq) (suffix : Bool),
    baAffixE suffix (.buf acts (.ok p) rel) h =
      (.ok ((if suffix then baRemovesuffix else baRemoveprefix) (runActs h acts).ba.seq p),
        runActs (runActs h acts) rel)) ∧
  (∀ (h : H) (o : Obj) (p : Seq) (suffix : Bool), o.buffer? = some p →
    baAffixE suffix (.obj o) h = (.ok ((if suffix then bytesRemovesuffix else bytesRemoveprefix) h.ba.seq p), h))

theorem affix_twin (s p : Seq) : baRemoveprefix s p = bytesRemoveprefix s p ∧ baRemovesuffix s p = bytesRemovesuffix s p := by
  constructor
  · unfold baRemoveprefix bytesRemoveprefix
    by_cases hp : p.length = 0
    · have : p = [] := List.eq_nil_of_length_eq_zero hp
      subst this; simp
    · have : p.length > 0 := by omega
      simp [this]
  · unfold baRemovesuffix bytesRemovesuffix
    by_cases hp : p.length = 0
    · have : p = [] := List.eq_nil_of_length_eq_zero hp
      subst this; simp
    · have : p.length > 0 := by omega
      simp [this]

theorem affixSpec_proven : AffixSpec := by
  refine ⟨affix_twin, ?_, ?_⟩
  · intro h acts rel p suffix
    cases suffix <;> simp [baAffixE, E.bind_app, getBuf_buf, curSeq, Buf.read, runCb_app]
  · intro h o p suffix hb
    cases suffix <;> simp [baAffixE, E.bind_app, getBuf_obj o p hb, curSeq, Buf.read, noRel, (affix_twin _ _).1,
      (affix_twin _ _).2]

/-- `bytearray.maketrans` is `_Py_bytes_maketrans` of the two buffers as their `__buffer__` gave them. -/
def BaMaketransSpec : Prop :=
  ∀ (h : H) (a1 r1 a2 r2 : List Act) (f t : Seq),
    baMaketransE (.buf a1 (.ok f) r1) (.buf a2 (.ok t) r2) h =
      (bytesMaketrans f t, runActs (runActs (runActs (runActs h a1) a2) r1) r2)

theorem baMaketransSpec_proven : BaMaketransSpec := by
  intro h a1 r1 a2 r2 f t
  simp [baMaketransE, E.bind_app, E.attempt_app, getBuf_buf, Buf.read, runCb_app]

/-- `bytearray_getitem_lock_held` (`sq_item`), :508-518, and `bytearray_getitem`: for an object whose
bytes are all written, the byte at an index of `range(len)` and `IndexError` outside, as list
indexing gives. -/
def GetItemRawSpec : Prop :=
  ∀ (b : BA) (i : Int), (∀ x ∈ b.data, 0 ≤ x) →
    baGetItemRaw b i =
      (if 0 ≤ i then match b.seq[i.toNat]? with
        | some c => .ok (c : Int)
        | none => .error (.indexError "bytearray index out of range")
      else .error (.indexError "bytearray index out of range"))

theorem getItemRawSpec_proven : GetItemRawSpec := by
  intro b i hd
  unfold baGetItemRaw
  by_cases h0 : 0 ≤ i
  · by_cases hl : i < b.size
    · have hl' : i.toNat < b.data.length := by simp [BA.size] at hl; omega
      have hx := hd _ (List.getElem_mem hl')
      have hs : b.seq[i.toNat]? = some (b.data[i.toNat]).toNat := by
        simp [BA.seq, hl']
      rw [hs]
      have hng : ¬ (i < 0 ∨ i ≥ b.size) := by omega
      simp only [hng, ↓reduceIte, h0]
      simp [List.getD, hl']
      omega
    · have hs : b.seq[i.toNat]? = none := by
        simp [BA.seq]; simp [BA.size] at hl; omega
      rw [hs]
      have hg : i < 0 ∨ i ≥ b.size := by omega
      simp [hg, h0]
  · have hg : i < 0 ∨ i ≥ b.size := by omega
    simp [hg, h0]

end PyLean.BytesObj.Bytes

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-- `bytearray_repeat_lock_held` (`b * n`), :439-469: a count `n ≤ 0` gives an empty bytearray,
`MemoryError` exactly when `len(b) > PyByteArray_SIZE_MAX // n`, and otherwise a new bytearray (no
exports) of `n` copies, whenever it fits in memory. -/
def BaRepeatSpec : Prop :=
  ∀ (b : BA) (n : Int),
    (n ≤ 0 → baRepeat b n = .ok {}) ∧
    (0 < n → b.size > Int.tdiv baSizeMax n → baRepeat b n = .error memoryError) ∧
    (0 < n → b.size * n < 2 ^ 46 →
      ∃ r, baRepeat b n = .ok r ∧ r.data = seqData (List.replicate n.toNat b.seq).flatten ∧ r.exports = 0)

theorem baRepeatSpec_proven : BaRepeatSpec := by
  intro b n
  have hs0 : 0 ≤ b.size := by simp [BA.size]
  refine ⟨?_, ?_, ?_⟩
  · intro hn
    unfold baRepeat
    have hc : (if n < 0 then 0 else n) = 0 := by split <;> omega
    simp only [hc, bind, Except.bind, pure, Except.pure]
    simp [Int.mul_zero, baFromStringAndSize, bytesSizeCheck]
  · intro hn hb
    unfold baRepeat
    have hc : (if n < 0 then 0 else n) = n := by split <;> omega
    simp [hc, hn, hb, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · intro hn hsz
    have hc : (if n < 0 then 0 else n) = n := by split <;> omega
    have hmax : baSizeMax = 2 ^ 63 - 1 - 33 := rfl
    have hd : ¬ b.size > Int.tdiv baSizeMax n := by
      rw [Int.tdiv_eq_ediv_of_nonneg (by rw [hmax]; omega)]
      intro hgt
      have h1 : (baSizeMax / n + 1) * n ≤ b.size * n := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
      have h2 : baSizeMax < (baSizeMax / n + 1) * n := Int.lt_ediv_add_one_mul_self _ hn
      rw [hmax] at h2 h1; omega
    have hpos : 0 ≤ b.size * n := Int.mul_nonneg hs0 (by omega)
    obtain ⟨r0, hr0⟩ := baFromStringAndSize_ok (b.size * n) hpos hsz
    by_cases hz : b.size * n = 0
    · have hsz0 : b.size = 0 := by
        rcases Int.mul_eq_zero.mp hz with h | h
        · exact h
        · omega
      have hd0 : b.data = [] := by simpa [BA.size] using hsz0
      refine ⟨{}, ?_, ?_, rfl⟩
      · unfold baRepeat
        simp only [hc, bind, Except.bind, pure, Except.pure, hn, hd, and_false, ↓reduceIte, hz]
        simp [baFromStringAndSize, bytesSizeCheck]
      · simp [BA.seq, hd0, seqData]
    · refine ⟨{ r0 with data := seqData (bytesRepeatFill (b.size * n).toNat b.seq) }, ?_, ?_, ?_⟩
      · unfold baRepeat
        simp [hc, bind, Except.bind, pure, Except.pure, hn, hd, hr0, hz]
      · show seqData _ = seqData _
        have hne : b.seq ≠ [] := by
          intro e
          have : b.data = [] := by simpa [BA.seq] using e
          apply hz; simp [BA.size, this]
        have hl : (b.size * n).toNat = n.toNat * b.seq.length := by
          have : b.seq.length = b.data.length := by simp [BA.seq]
          rw [this]; simp only [BA.size]
          rw [Int.toNat_mul (by omega) (by omega)]
          simp [Nat.mul_comm]
        rw [hl, repeatFill_proven b.seq n.toNat hne (by omega)]
      · exact (allocFailureSilent_proven.1 none _ r0 hr0).1

end PyLean.BytesObj.Bytes
