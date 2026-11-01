import PyLean.BytesObj.Mem.Hex

/-!
The remaining behaviour: the rejections of `cast` and `pack_single`, garbage collection,
`repr`, Fortran strides, `tobytes` on 1-D views, `toreadonly`, the constructors.
-/

namespace PyLean.BytesObj.Mem

open PyLean

/-- The refusals of `memoryview.cast`, in the order of the source, :1458-1482, each leaving
the state alone. Hypotheses: a live, unrestricted view. -/
def CastRejections : Prop :=
  ∀ (st : St) (self : Nat) (f : List Char) (s : Option ShapeArg),
    baseInaccessible st self = false → (st.mv self).flags.restricted = false →
    let c := memoryviewCast self f s st
    ((st.mv self).flags.isC = false →
      c = (.error (.typeError "memoryview: casts are restricted to C-contiguous views"), st)) ∧
    ((st.mv self).flags.isC = true → (s.isSome = true ∨ (st.mv self).view.ndim ≠ 1) →
      HasZero (st.mv self).view →
      c = (.error (.typeError "memoryview: cannot cast view with zeros in shape or strides"), st))

theorem castRejections_proven : CastRejections := by
  intro st self f s hl hr
  dsimp only
  constructor
  · intro h
    simp only [memoryviewCast, M.bind_app, checkReleased_ok _ _ hl, checkRestricted_ok _ _ hr, M.get, h,
      Bool.not_false, ↓reduceIte, M.throw_app]
  · intro h1 h2 h3
    have hz : ((s.isSome || (st.mv self).view.ndim != 1) && zeroInShape (st.mv self).view) = true := by
      have h3' := (zeroInShape_iff _).2 h3
      rcases h2 with h | h <;> simp [h, h3']
    simp only [memoryviewCast, M.bind_app, checkReleased_ok _ _ hl, checkRestricted_ok _ _ hr, M.get, h1,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, hz, M.throw_app]

/-- `pack_single` on values of the wrong kind: a non-integer in an integer format raises
`TypeError("memoryview: invalid type for format ...")`, and in the format `c` anything but
`bytes` does, with `ValueError` for `bytes` of another length (:1995-1999). Nothing is written.
Hypothesis: a live view. -/
def PackTypeErrors : Prop :=
  ∀ (st : St) (self : Nat) (ptr : Int) (c : Char) (lo hi : Int) (k : Nat) (s : List Char),
    intRange c = some (lo, hi, k) → baseInaccessible st self = false →
    packSingle self ptr (.str s) [c] st = (.error (typeErrorInt [c]), st) ∧
    packSingle self ptr (.str s) ['c'] st = (.error (typeErrorInt ['c']), st) ∧
    packSingle self ptr (.int lo) ['c'] st = (.error (typeErrorInt ['c']), st) ∧
    packSingle self ptr (.bytes []) ['c'] st = (.error (valueErrorInt ['c']), st) ∧
    packSingle self ptr (.bytes [0, 0]) ['c'] st = (.error (valueErrorInt ['c']), st)

theorem packTypeErrors_proven : PackTypeErrors := by
  intro st self ptr c lo hi k s hc hl
  refine ⟨?_, by simp [packSingle, cc, M.throw_app], by simp [packSingle, cc, M.throw_app],
    by simp [packSingle, cc, M.throw_app], by simp [packSingle, cc, M.throw_app]⟩
  unfold intRange at hc
  split at hc <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hc
  all_goals simp only [packSingle, cc, List.getD_cons_zero, M.bind_app, M.mapErr, pylongAsLd, pylongAsLu,
    pylongAsLld, pylongAsLlu, pylongAsZd, pylongAsZu, numberIndex, M.throw_app, fixErrorInt]

/-- A view in a reference cycle (`memory_clear`, :1171-1180) is released like any other if
it has no exports, and left alone if it has. -/
def ClearIsRelease : Prop :=
  ∀ (st : St) (i : Nat),
    ((st.mv i).exports = 0 → memoryClear i st = memoryRelease i st) ∧
    ((st.mv i).exports ≠ 0 → memoryClear i st = (.ok (), st)) ∧
    (memoryRepr i st).2 = st

theorem clearIsRelease_proven : ClearIsRelease := by
  intro st i
  refine ⟨fun h => ?_, fun h => ?_, rfl⟩
  · simp [memoryClear, getExports, h]
  · simp [memoryClear, getExports, h]

/-- `repr` says whether the view is released, by `self->flags` only (:2375-2383). -/
def ReprReleased : Prop :=
  ∀ (st : St) (i : Nat), (memoryRepr i st).1 =
    .ok (if (st.mv i).flags.released then "<released memory" else "<memory")

theorem reprReleased_proven : ReprReleased := fun _ _ => rfl

theorem fLoop_fStrides (l : List Int) (sd : Int) : fLoop l (fStrides sd l) sd = true := by
  induction l generalizing sd with
  | nil => rfl
  | cons d ds ih =>
    simp only [fStrides, fLoop, ne_eq, not_true_eq_false, and_false, ↓reduceIte, ih]

/-- Every array `init_fortran_strides_from_shape` lays out is Fortran-contiguous, for every
shape (:480-490; `buffer_to_contiguous` with order `'F'`). Hypotheses: `len`, `shape` and
`strides` as that function leaves them. -/
def FortranStrides : Prop :=
  ∀ (v : Buf) (sh : List Int), v.shape = some sh → v.strides = some (fStrides v.itemsize sh) →
    isFortranContiguous v = true

theorem fortranStrides_proven : FortranStrides := by
  intro v sh hs hst
  unfold isFortranContiguous
  split
  · rfl
  · rw [hst, hs]
    exact fLoop_fStrides _ _

/-- `PyBuffer_ToContiguous` normalises a view with full information to itself. -/
theorem fb_1d (v : Buf) (n d : Int) (f : List Char) (h1 : v.ndim = 1) (hsh : v.shape = some [n])
    (hst : v.strides = some [d]) (hsub : v.suboffsets = none) (hf : v.format = some f) :
    { initSharedValues v v with
      shape := (initShapeStrides v).1, strides := (initShapeStrides v).2,
      suboffsets := initSuboffsets v } = v := by
  cases v
  simp_all [initShapeStrides, initSharedValues, initSuboffsets]

/-- `m.tobytes()` of a 1-D view, for every stride: the items in order, by `memcpy` when the
view is contiguous and through `buffer_to_contiguous` when it is not. The two branches of
`PyBuffer_ToContiguous` (:1062-1065, :1084) give the same bytes. Hypotheses: a live view with
`len == n * itemsize`, `itemsize > 0`. -/
def Tobytes1D : Prop :=
  ∀ (st : St) (self : Nat) (n d : Int) (f : List Char),
    Live1D st self n d f → 0 < (st.mv self).view.itemsize →
    (st.mv self).view.len = n * (st.mv self).view.itemsize →
    memoryviewTobytes self none st =
      (.ok (flatBytes st.mem (st.mv self).view.itemsize [n] [d] none (st.mv self).view.buf), st)

theorem tobytes1D_proven : Tobytes1D := by
  intro st self n d f hL hit hlen
  have hmain : pyBufferToContiguous st.mem (st.mv self).view (st.mv self).view.len 'C' =
      .ok (flatBytes st.mem (st.mv self).view.itemsize [n] [d] none (st.mv self).view.buf) := by
    have hsb := hL.subs
    have hsh := hL.shape
    have hst := hL.strides
    have hnd := hL.ndim
    have hfm := hL.format
    have hnn := hL.nonneg
    generalize hv : (st.mv self).view = v at *
    by_cases hc : pyBufferIsContiguous v 'C' = true
    · simp only [pyBufferToContiguous, ne_eq, not_true_eq_false, ↓reduceIte, hc]
      congr 1
      by_cases hn0 : n = 0
      · subst hn0
        simp [hlen, rdBytes, flatBytes, addrs, walk]
      · have hlenne : v.len ≠ 0 := by
          rw [hlen]
          exact Int.ne_of_gt (Int.mul_pos (by omega) hit)
        have hcc : n ≤ 1 ∨ d = v.itemsize := by
          simp only [pyBufferIsContiguous, hsb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
            isCContiguous, hlenne, hst, hsh, Option.getD_some, hnd, cLoop, List.getD_cons_zero] at hc
          by_cases h : n > 1 ∧ d ≠ v.itemsize
          · simp [h] at hc
          · omega
        have hflat : flatBytes st.mem v.itemsize [n] [d] none v.buf =
            (walk d n.toNat v.buf).flatMap fun p => rdBytes st.mem p v.itemsize.toNat := by
          simp [flatBytes, addrs, adjustPtr_none]
        rw [hflat, hlen]
        rcases hcc with h1 | h1
        · have hn1 : n = 1 := by omega
          subst hn1
          simp [walk]
        · subst h1
          rw [Int.toNat_mul hnn (by omega)]
          have := rdBytes_walk st.mem v.itemsize.toNat n.toNat v.buf
          rw [Int.toNat_of_nonneg (by omega)] at this
          exact this
    · have hcf : pyBufferIsContiguous v 'C' = false := by simpa using hc
      simp only [pyBufferToContiguous, ne_eq, not_true_eq_false, ↓reduceIte, hcf, Bool.false_eq_true]
      have hfb := fb_1d v n d f hnd hsh hst hsb hfm
      have ht := tobytesC_proven st.mem v [n] [d] hsh hst (by simp) (by simp [hnd])
        (by simpa using hnn) hit (by simp [prod, hlen])
      rw [hsb] at ht
      simp only [initShapeStrides, hfb] at *
      rw [← ht]
      congr 1
  have hc := checkReleased_ok st self hL.live
  simp only [memoryviewTobytes, M.bind_app, hc, M.pure_app, M.get, M.lift, hmain, parseOrder]

/-- `m.toreadonly()` is a new read-only view of the same buffer and shape; `m` is unchanged
and the new view counts on the managed buffer. Hypotheses: a live, unrestricted 1-D view. -/
def ToReadonlySpec : Prop :=
  ∀ (st : St) (self : Nat) (n d : Int) (f : List Char), Live1D st self n d f →
    let r := memoryviewToreadonly self st
    let i := st.mvs.length
    r.1 = .ok i ∧ (r.2.mv i).view = { (st.mv self).view with readonly := true } ∧
      (r.2.mv self).view = (st.mv self).view ∧ r.2.mem = st.mem ∧
      (r.2.mb (st.mv self).mbuf).exports = (st.mb (st.mv self).mbuf).exports + 1

theorem toReadonlySpec_proven : ToReadonlySpec := by
  intro st self n d f hL
  have hview := viewCopy_1d _ n d f hL.ndim hL.shape hL.strides hL.subs hL.format
  have ⟨hr1, hA⟩ := mbufAddView_added (st.mv self).mbuf (st.mv self).view st (by rw [hL.ndim]; omega)
  rw [hview] at hA
  dsimp only
  simp only [memoryviewToreadonly, M.bind_app, checkReleased_ok _ _ hL.live,
    checkRestricted_ok _ _ hL.unres, M.get]
  rcases hrr : mbufAddView (st.mv self).mbuf (some (st.mv self).view) st with ⟨r1, st1⟩
  rw [hrr] at hr1 hA
  simp only at hr1 hA
  subst hr1
  simp only [M.modify, M.pure_app]
  have hn : st.mvs.length < st1.mvs.length := by rw [hA.len]; omega
  refine ⟨trivial, ?_, ?_, ?_, ?_⟩
  · rw [St.mv_setMv _ _ _ hn, hA.new]
  · rw [St.mv_setMv_ne _ _ _ _ (by have := hL.valid; omega), hA.old _ hL.valid]
  · exact hA.mem
  · rw [St.mb_setMv]; exact hA.exports hL.mbuf

/-- Constructing from a memoryview shares its managed buffer and checks it is usable; from
anything that is not a buffer the constructor raises `TypeError`, from `memoryview(obj)` to
`_from_flags`, with the type's name in the message (:800-825). -/
def NewViewRules : Prop :=
  ∀ (st : St) (self : Nat) (n d : Int) (f : List Char) (flags : Nat) (k : Int),
    Live1D st self n d f →
    (let r := memoryviewNew (.view self) st
     let i := st.mvs.length
     r.1 = .ok i ∧ (r.2.mv i).view = (st.mv self).view ∧ (r.2.mv i).mbuf = (st.mv self).mbuf ∧
       r.2.mem = st.mem ∧ memoryviewFromFlags (.view self) flags st = r ∧
       (r.2.mb (st.mv self).mbuf).exports = (st.mb (st.mv self).mbuf).exports + 1) ∧
    memoryviewNew (.int k) st =
      (.error (.typeError "memoryview: a bytes-like object is required, not 'int'"), st) ∧
    memoryviewNew .none st =
      (.error (.typeError "memoryview: a bytes-like object is required, not 'NoneType'"), st)

theorem newViewRules_proven : NewViewRules := by
  intro st self n d f flags k hL
  have hview := viewCopy_1d _ n d f hL.ndim hL.shape hL.strides hL.subs hL.format
  have ⟨hr1, hA⟩ := mbufAddView_added (st.mv self).mbuf (st.mv self).view st (by rw [hL.ndim]; omega)
  rw [hview] at hA
  have e : ∀ fl, memoryViewFromObjectAndFlags (.view self) fl st =
      mbufAddView (st.mv self).mbuf (some (st.mv self).view) st := by
    intro fl
    simp only [memoryViewFromObjectAndFlags, M.bind_app, checkReleased_ok _ _ hL.live,
      checkRestricted_ok _ _ hL.unres, M.get]
  refine ⟨?_, ?_, ?_⟩
  · dsimp only
    simp only [memoryviewNew, memoryViewFromObject, memoryviewFromFlags, e]
    refine ⟨hr1, ?_, ?_, hA.mem, trivial, hA.exports hL.mbuf⟩
    · rw [hA.new]
    · rw [hA.new]
  · simp [memoryviewNew, memoryViewFromObject, memoryViewFromObjectAndFlags, M.throw_app, Obj.typeName,
      toString]
  · simp [memoryviewNew, memoryViewFromObject, memoryViewFromObjectAndFlags, M.throw_app, Obj.typeName,
      toString]

end PyLean.BytesObj.Mem
