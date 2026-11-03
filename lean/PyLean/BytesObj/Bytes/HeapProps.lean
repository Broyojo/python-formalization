import PyLean.BytesObj.Bytes.Heap

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
