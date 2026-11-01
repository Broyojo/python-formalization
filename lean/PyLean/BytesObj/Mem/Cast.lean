import PyLean.BytesObj.Mem.Format

/-!
`memoryview.cast`: the 1-D step, the N-D step, and C-contiguity of the result.
-/

namespace PyLean.BytesObj.Mem

open PyLean

/-- A dimension of the view has length 0. -/
def HasZero (v : Buf) : Prop := ∃ i, i < v.ndim ∧ (v.shape.getD []).getD i 1 = 0

theorem any_take_zero (l : List Int) (n : Nat) :
    (l.take n).any (· == 0) = true ↔ ∃ i, i < n ∧ l.getD i 1 = 0 := by
  induction l generalizing n with
  | nil => simp
  | cons a as ih =>
    cases n with
    | zero => simp
    | succ n =>
      simp only [List.take_succ_cons, List.any_cons, Bool.or_eq_true, beq_iff_eq, ih]
      constructor
      · rintro (h | ⟨i, hi, e⟩)
        · exact ⟨0, by omega, by simpa using h⟩
        · exact ⟨i + 1, by omega, by simpa using e⟩
      · rintro ⟨i, hi, e⟩
        cases i with
        | zero => exact Or.inl (by simpa using e)
        | succ i => exact Or.inr ⟨i, by omega, by simpa using e⟩

/-- `zero_in_shape`, :1412-1423: true exactly when a dimension has length 0. -/
theorem zeroInShape_iff (v : Buf) : zeroInShape v = true ↔ HasZero v :=
  any_take_zero _ _

theorem zeroInShape_false (v : Buf) (h : ¬ HasZero v) : zeroInShape v = false := by
  cases hz : zeroInShape v with
  | false => rfl
  | true => exact absurd ((zeroInShape_iff v).1 hz) h

/-- What `cast_to_1D` leaves in the view. -/
def castView (view : Buf) (fstr : List Char) (size : Int) : Buf :=
  { obj := view.obj, buf := view.buf, len := view.len, itemsize := size, readonly := view.readonly,
    ndim := 1, format := some fstr, shape := some [view.len.tdiv size], strides := some [size],
    suboffsets := none, hook := view.hook }

/-- `m.cast(format)` on a live C-contiguous view, with a native `format`, when one side has
byte size and the length is a multiple of the new item size, gives a new view registered
with the same managed buffer: same memory, same byte length, 1-D, `shape * itemsize ==
len` ("All casts must result in views that will have the exact byte size of the original
input", :1435). `self` keeps its contents. Hypotheses: `self` and its managed buffer are
live objects; the rest are the conditions the function checks. -/
def Cast1DSpec : Prop :=
  ∀ (st : St) (self : Nat) (format : List Char) (c : Char) (size : Int) (fstr : List Char),
    self < st.mvs.length → (st.mv self).mbuf < st.mbufs.length →
    baseInaccessible st self = false → (st.mv self).flags.restricted = false →
    (st.mv self).flags.isC = true →
    ((st.mv self).view.ndim = 1 ∨ ¬ HasZero (st.mv self).view) →
    (∀ ch ∈ format, ch.toNat < 128) →
    getNativeFmtchar format = some (c, size) →
    getNativeFmtstr format = some fstr →
    (srcIsByte (st.mv self).view = true ∨ isByteFormat c = true) →
    (st.mv self).view.len.tmod size = 0 →
    let r := memoryviewCast self format none st
    let n := st.mvs.length
    let view := (st.mv self).view
    r.1 = .ok n ∧ (r.2.mv n).view = castView view fstr size ∧
      (r.2.mv n).flags = initFlags (castView view fstr size) ∧
      (r.2.mv n).mbuf = (st.mv self).mbuf ∧ r.2.mem = st.mem ∧
      (r.2.mv self).view = view ∧
      (r.2.mb (st.mv self).mbuf).exports = (st.mb (st.mv self).mbuf).exports + 1

theorem any_ascii_false (format : List Char) (h : ∀ ch ∈ format, ch.toNat < 128) :
    (format.any fun c => decide (c.toNat ≥ 128)) = false := by
  simp only [List.any_eq_false, decide_eq_true_eq]
  intro x hx
  have := h x hx
  omega

theorem mv_append_new (st : St) (x : MV) :
    St.mv { st with mvs := st.mvs ++ [x] } st.mvs.length = x := by
  simp [St.mv, List.getD_eq_getElem?_getD]

theorem mv_append_old (st : St) (x : MV) (i : Nat) (h : i < st.mvs.length) :
    St.mv { st with mvs := st.mvs ++ [x] } i = st.mv i := by
  simp [St.mv, List.getD_eq_getElem?_getD, List.getElem?_append_left, h]

/-- Registering a new view `x` with managed buffer `k`. -/
structure Added (st st1 : St) (k : Nat) (x : MV) : Prop where
  new : st1.mv st.mvs.length = x
  old : ∀ i, i < st.mvs.length → st1.mv i = st.mv i
  len : st1.mvs.length = st.mvs.length + 1
  mem : st1.mem = st.mem
  mbufs : st1.mbufs.length = st.mbufs.length
  exports : k < st.mbufs.length → (st1.mb k).exports = (st.mb k).exports + 1
  master : k < st.mbufs.length → (st1.mb k).master = (st.mb k).master
  released : k < st.mbufs.length → (st1.mb k).released = (st.mb k).released
  other : ∀ j, j ≠ k → st1.mb j = st.mb j
  iters : st1.iters = st.iters
  unhash : st1.unhashable = st.unhashable

theorem added_of (st : St) (k : Nat) (x : MV) :
    let st0 : St := { st with mvs := st.mvs ++ [x] }
    Added st (st0.setMb k { st0.mb k with exports := (st0.mb k).exports + 1 }) k x := by
  intro st0
  refine ⟨mv_append_new st x, fun i h => mv_append_old st x i h, by simp [St.setMb, st0], rfl,
    by simp [St.setMb, st0], ?_, ?_, ?_, ?_, rfl, rfl⟩
  · intro h
    rw [St.mb_setMb st0 k _ (by simpa [st0] using h)]
    rfl
  · intro h
    rw [St.mb_setMb st0 k _ (by simpa [st0] using h)]
    rfl
  · intro h
    rw [St.mb_setMb st0 k _ (by simpa [st0] using h)]
    rfl
  · intro j hj
    rw [St.mb_setMb_ne st0 k j _ (Ne.symm hj)]
    rfl

theorem mbufAddIncompleteView_added (k : Nat) (src : Buf) (ndim : Nat) (st : St) :
    (mbufAddIncompleteView k (some src) ndim st).1 = .ok st.mvs.length ∧
    Added st (mbufAddIncompleteView k (some src) ndim st).2 k
      { mbuf := k, view := initSharedValues { ndim := ndim } src } := by
  exact ⟨rfl, added_of st k _⟩

theorem castTo1D_spec (i : Nat) (format : List Char) (st : St) (c : Char) (size : Int)
    (fstr : List Char) (hany : (format.any fun c => decide (c.toNat ≥ 128)) = false)
    (hf : getNativeFmtchar format = some (c, size)) (hs : getNativeFmtstr format = some fstr)
    (hbyte : srcIsByte (st.mv i).view = true ∨ isByteFormat c = true)
    (hmod : (st.mv i).view.len.tmod size = 0) :
    castTo1D i format st =
      (.ok (), st.setMv i { st.mv i with
        view := { (st.mv i).view with
          format := some fstr, itemsize := size, ndim := 1,
          shape := some [Int.tdiv (st.mv i).view.len size], strides := some [size], suboffsets := none },
        flags := initFlags { (st.mv i).view with
          format := some fstr, itemsize := size, ndim := 1,
          shape := some [Int.tdiv (st.mv i).view.len size], strides := some [size], suboffsets := none } }) := by
  have hb : (!srcIsByte (st.mv i).view && !isByteFormat c) = false := by
    rcases hbyte with h | h <;> simp [h]
  unfold castTo1D
  simp only [M.bind_app, M.get, hany, Bool.false_eq_true, ↓reduceIte, hf, hs, hmod, hb, ne_eq,
    not_true_eq_false, M.pure_app, M.set]

theorem cast1DSpec_proven : Cast1DSpec := by
  intro st self format c size fstr hself hmb hrel hres hC hz hasc hf hs hbyte hmod
  have hany := any_ascii_false format hasc
  have hz' : ((Option.isSome (none : Option ShapeArg) || (st.mv self).view.ndim != 1) &&
      zeroInShape (st.mv self).view) = false := by
    rcases hz with h | h
    · simp [h]
    · simp [zeroInShape_false _ h]
  dsimp only
  unfold memoryviewCast
  simp only [M.bind_app, checkReleased_ok _ _ hrel, checkRestricted_ok _ _ hres, M.get, hC,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, hz', M.pure_app]
  have ⟨hr1, hA⟩ := mbufAddIncompleteView_added (st.mv self).mbuf (st.mv self).view
    (if (1 : Nat) = 0 then 1 else 1) st
  rcases hrr : mbufAddIncompleteView (st.mv self).mbuf (some (st.mv self).view)
    (if (1 : Nat) = 0 then 1 else 1) st with ⟨r1, st1⟩
  rw [hrr] at hr1 hA
  dsimp only at hr1 hA
  subst hr1
  simp only []
  have hview : (st1.mv st.mvs.length).view = initSharedValues { ndim := 1 } (st.mv self).view := by
    rw [hA.new]; rfl
  have hn : st.mvs.length < st1.mvs.length := by rw [hA.len]; omega
  have hc := castTo1D_spec st.mvs.length format st1 c size fstr hany hf hs
    (by rw [hview]; simpa [srcIsByte, initSharedValues] using hbyte)
    (by rw [hview]; simpa [initSharedValues] using hmod)
  simp only [M.onError, M.bind_app, hc, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
    M.pure_app]
  have hrec : ({ (st1.mv st.mvs.length).view with
      format := some fstr, itemsize := size, ndim := 1,
      shape := some [Int.tdiv (st1.mv st.mvs.length).view.len size], strides := some [size],
      suboffsets := none } : Buf) = castView (st.mv self).view fstr size := by
    rw [hview]; rfl
  rw [hrec]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [St.mv_setMv _ _ _ hn]
  · rw [St.mv_setMv _ _ _ hn]
  · rw [St.mv_setMv _ _ _ hn]
    show (st1.mv st.mvs.length).mbuf = _
    rw [hA.new]
  · simpa using hA.mem
  · rw [St.mv_setMv_ne _ _ _ _ (by omega), hA.old _ hself]
  · rw [St.mb_setMv]
    exact hA.exports hmb

/-- `copy_shape` multiplies the elements into `len`, all of them positive. -/
theorem copyShape_ok (items : List Obj) (len l : Int) (s : List Int)
    (h : copyShape items len = .ok (l, s)) :
    l = s.foldl (· * ·) len ∧ (∀ x ∈ s, 0 < x) ∧ s.length = items.length := by
  induction items generalizing len l s with
  | nil =>
    simp only [copyShape, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | cons tmp rest ih =>
    simp only [copyShape] at h
    split at h
    · simp at h
    · rename_i v _
      simp only [bind, Except.bind] at h
      split at h
      · simp at h
      · rename_i x hx
        split at h
        · simp at h
        · rename_i hpos
          split at h
          · simp at h
          · simp only [pure, Except.pure] at h
            split at h
            · simp at h
            · rename_i a hrec
              have : a = (a.1, a.2) := rfl
              rw [this] at hrec
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              have ⟨h1, h2, h3⟩ := ih _ _ _ hrec
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨by simpa using h1, ?_, by simp [h3]⟩
              intro y hy
              simp only [List.mem_cons] at hy
              rcases hy with rfl | hy
              · omega
              · exact h2 y hy

theorem cLoop_congr (a b : List Int) (x y : Int) (n : Nat) (sd : Int) (ha : n ≤ a.length)
    (hb : n ≤ b.length) : cLoop (a ++ [x]) (b ++ [y]) n sd = cLoop a b n sd := by
  induction n generalizing sd with
  | zero => rfl
  | succ n ih =>
    simp only [cLoop]
    have h1 : (a ++ [x]).getD n 0 = a.getD n 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, show n < a.length by omega]
    have h2 : (b ++ [y]).getD n 0 = b.getD n 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, show n < b.length by omega]
    rw [h1, h2]
    split
    · rfl
    · exact ih _ (by omega) (by omega)

theorem fStrides_length (sd : Int) (l : List Int) : (fStrides sd l).length = l.length := by
  induction l generalizing sd with
  | nil => rfl
  | cons d ds ih => simp [fStrides, ih]

theorem cLoop_cStrides (rs : List Int) (sd : Int) :
    cLoop rs.reverse (fStrides sd rs).reverse rs.length sd = true := by
  induction rs generalizing sd with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.reverse_cons, fStrides, List.length_cons, cLoop]
    have h1 : (ds.reverse ++ [d]).getD ds.length 0 = d := by
      simp [List.getD_eq_getElem?_getD]
    have h2 : ((fStrides (sd * d) ds).reverse ++ [sd]).getD ds.length 0 = sd := by
      have : ds.length = (fStrides (sd * d) ds).reverse.length := by simp [fStrides_length]
      rw [this]
      simp [List.getD_eq_getElem?_getD]
    rw [h1, h2]
    simp only [ne_eq, not_true_eq_false, and_false, ↓reduceIte]
    rw [cLoop_congr _ _ _ _ _ _ (by simp) (by simp [fStrides_length])]
    exact ih _

/-- Every array `init_strides_from_shape` lays out is C-contiguous, for every shape, as
the comment of `cast_to_ND` says ("The result array will be C-contiguous"). -/
theorem isCContiguous_cStrides (v : Buf) (sh : List Int) (hs : v.shape = some sh)
    (hst : v.strides = some (cStrides v.itemsize sh)) (hn : v.ndim = sh.length) :
    isCContiguous v = true := by
  unfold isCContiguous
  split
  · rfl
  · rw [hst, hs, hn]
    have := cLoop_cStrides sh.reverse v.itemsize
    simpa [cStrides] using this

/-- A shape cast: if `cast_to_ND` succeeds on the 1-D view left by `cast_to_1D` (no
suboffsets, by the assertion at :1387), then with `ndim == 0` the view has no shape or strides and
one item, and otherwise it has `ndim == len(shape)`, the given shape, C strides,
`product(shape) * itemsize == len` and positive dimensions; either way it reports `c_contiguous`.
A shape of another byte size is refused, leaving the state alone (:1402-1406). Hypothesis: `i` is
a live view. -/
def CastNDSpec : Prop :=
  ∀ (st st' : St) (i ndim : Nat) (items : List Obj) (u : Unit),
    i < st.mvs.length → (st.mv i).view.suboffsets = none → ndim = items.length →
    (castToND i items ndim st = (.ok u, st') →
      (ndim = 0 → let v := (st'.mv i).view
        v.ndim = 0 ∧ v.shape = none ∧ v.strides = none ∧ v.len = v.itemsize ∧
        v.len = (st.mv i).view.len ∧ (st'.mv i).flags.isC = true) ∧
      (0 < ndim → ∃ sh, let v := (st'.mv i).view
        v.shape = some sh ∧ v.ndim = ndim ∧ v.strides = some (cStrides v.itemsize sh) ∧
        v.len = sh.foldl (· * ·) 1 * v.itemsize ∧ v.len = (st.mv i).view.len ∧
        (∀ x ∈ sh, 0 < x) ∧ (st'.mv i).flags.isC = true)) ∧
    (ndim = 0 → (st.mv i).view.len ≠ (st.mv i).view.itemsize →
      castToND i items ndim st =
        (.error (.typeError "memoryview: product(shape) * itemsize != buffer size"), st)) ∧
    (∀ l sh, 0 < ndim → copyShape items (st.mv i).view.itemsize = .ok (l, sh) → (st.mv i).view.len ≠ l →
      castToND i items ndim st =
        (.error (.typeError "memoryview: product(shape) * itemsize != buffer size"), st))

theorem foldl_mul (l : List Int) (a b : Int) :
    l.foldl (· * ·) (a * b) = l.foldl (· * ·) a * b := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [show a * b * x = a * x * b by simp [Int.mul_comm, Int.mul_left_comm], ih]

theorem foldl_mul_one (l : List Int) (a : Int) : l.foldl (· * ·) a = l.foldl (· * ·) 1 * a := by
  have := foldl_mul l 1 a
  simpa using this

theorem initFlags_isC_of (v : Buf) (sh : List Int) (hvs : v.suboffsets = none)
    (hvsh : v.shape = some sh) (hvst : v.strides = some (cStrides v.itemsize sh))
    (hn : v.ndim = sh.length) (hpos : 0 < v.ndim) : (initFlags v).isC = true := by
  unfold initFlags
  have hC := isCContiguous_cStrides v sh hvsh hvst hn
  generalize hd : v.ndim = d at hn hpos
  match d, hpos, hn with
  | 1, _, hn =>
    match sh, hn with
    | [a], _ =>
      simp [hvs, mvContiguousNdim1, hvst, cStrides, fStrides, Flags.isC]
  | n + 2, _, hn =>
    simp [hvs, Flags.isC, pyBufferIsContiguous, hC]

theorem castND_pos (st st' : St) (i ndim : Nat) (items : List Obj) (u : Unit)
    (hi : i < st.mvs.length) (hsub : (st.mv i).view.suboffsets = none) (hnd : ndim = items.length)
    (hpos : 0 < ndim) (h : castToND i items ndim st = (.ok u, st')) :
    ∃ sh, let v := (st'.mv i).view
      v.shape = some sh ∧ v.ndim = ndim ∧ v.strides = some (cStrides v.itemsize sh) ∧
      v.len = sh.foldl (· * ·) 1 * v.itemsize ∧ v.len = (st.mv i).view.len ∧
      (∀ x ∈ sh, 0 < x) ∧ (st'.mv i).flags.isC = true := by
  have hnz : ¬ ndim = 0 := by omega
  unfold castToND at h
  rcases hc : copyShape items (st.mv i).view.itemsize with e | ⟨l, sh⟩
  · simp [M.bind_app, M.get, hnz, M.lift, hc, M.throw_app] at h
  · have ⟨h1, h2, h3⟩ := copyShape_ok _ _ _ _ hc
    by_cases hl : (st.mv i).view.len = l
    · simp only [M.bind_app, M.get, hnz, ↓reduceIte, M.lift, hc, M.pure_app, hl, ne_eq,
        not_true_eq_false, M.set, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      rw [St.mv_setMv _ _ _ hi]
      dsimp only
      refine ⟨sh, rfl, rfl, rfl, ?_, hl.symm, h2, ?_⟩
      · rw [h1]; exact foldl_mul_one _ _
      · exact initFlags_isC_of _ sh hsub rfl rfl (by simp only; omega) hpos
    · simp [M.bind_app, M.get, hnz, M.lift, hc, M.pure_app, hl, M.throw_app] at h

theorem castNDSpec_proven : CastNDSpec := by
  intro st st' i ndim items u hi hsub hnd
  refine ⟨fun h => ⟨fun h0 => ?_, fun hpos => castND_pos st st' i ndim items u hi hsub hnd hpos h⟩,
    fun h0 hne => ?_, fun l sh hpos hc hne => ?_⟩
  · subst h0
    unfold castToND at h
    by_cases hl : (st.mv i).view.len = (st.mv i).view.itemsize
    · simp only [M.bind_app, M.get, ↓reduceIte, M.pure_app, hl, ne_eq, not_true_eq_false, M.set,
        Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      rw [St.mv_setMv _ _ _ hi]
      dsimp only
      refine ⟨rfl, rfl, rfl, hl.symm ▸ rfl, hl.symm, ?_⟩
      simp [initFlags, hsub, Flags.isC]
    · simp [M.bind_app, M.get, M.pure_app, hl, M.throw_app] at h
  · subst h0
    unfold castToND
    simp [M.bind_app, M.get, M.pure_app, hne, M.throw_app]
  · have hnz : ¬ ndim = 0 := by omega
    unfold castToND
    simp [M.bind_app, M.get, hnz, M.lift, hc, M.pure_app, hne, M.throw_app]

/-- `cast_to_ND` when the shape fits. -/
theorem castToND_ok (i : Nat) (items : List Obj) (ndim : Nat) (st : St) (l : Int) (sh : List Int)
    (hz : ndim ≠ 0) (hc : copyShape items (st.mv i).view.itemsize = .ok (l, sh))
    (hl : (st.mv i).view.len = l) :
    castToND i items ndim st =
      (.ok (), st.setMv i { st.mv i with
        view := { (st.mv i).view with
          ndim := ndim, shape := some sh, strides := some (cStrides (st.mv i).view.itemsize sh) },
        flags := initFlags { (st.mv i).view with
          ndim := ndim, shape := some sh, strides := some (cStrides (st.mv i).view.itemsize sh) } }) := by
  unfold castToND
  simp only [M.bind_app, M.get, hz, ↓reduceIte, M.lift, hc, M.pure_app, hl, ne_eq, not_true_eq_false, M.set]

end PyLean.BytesObj.Mem
