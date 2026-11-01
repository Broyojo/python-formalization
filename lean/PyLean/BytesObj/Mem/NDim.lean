import PyLean.BytesObj.Mem.Effects

/-!
Views of any number of dimensions: slices against `tolist`, `hash`, and a 0-dim `tolist`.
-/

namespace PyLean.BytesObj.Mem

open PyLean
open PyLean.RangeSlice (Slice sliceIndices IsLen)

/-- The rows of a result of `tolist`. -/
def Tree.kids : Tree → List Tree
  | .node l => l
  | .leaf _ => []

/-- Row at address `p` of the nested list `tolist` builds. -/
def rowOf (m : Mem) (g : Int → Item) (rest rs : List Int) (subs : Option (List Int)) (p : Int) : Tree :=
  match rest with
  | [] => .leaf (g (adjustPtr m p subs 0))
  | x :: xs => treeOf m g (x :: xs) rs (subTail subs) (adjustPtr m p subs 0)

theorem treeOf_rows (m : Mem) (g : Int → Item) (n : Int) (rest strs : List Int)
    (subs : Option (List Int)) (ptr : Int) :
    (treeOf m g (n :: rest) strs subs ptr).kids =
      (walk (strs.getD 0 0) n.toNat ptr).map (rowOf m g rest (strs.drop 1) subs) := by
  cases rest with
  | nil =>
    simp only [treeOf, Tree.kids]
    rfl
  | cons x xs =>
    simp only [treeOf, Tree.kids]
    rfl

theorem initFlags_released (v : Buf) : (initFlags v).released = false := by
  unfold initFlags
  dsimp only
  split <;> first | rfl | (split <;> first | rfl | (split <;> rfl))

theorem adjustFmt_format (v w : Buf) (h : v.format = w.format) : adjustFmt v = adjustFmt w := by
  simp only [adjustFmt, h]

theorem foldl_prod (l : List Int) : l.foldl (· * ·) 1 = prod l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, Int.one_mul, prod]
    rw [foldl_mul_one, ih, Int.mul_comm]

/-- `init_len`, :597-606: the product of the shape times `itemsize`. -/
theorem initLen_prod (l : List Int) (it : Int) : initLen l it = prod l * it := by
  simp only [initLen, foldl_prod]

/-- `m[s].tolist()` is `m.tolist()[s]` for a view of any number of dimensions, native format,
strides and suboffsets, and every slice with a non-zero step: the rows are those of
`range(*s.indices(n))`, in that order. Hypotheses: a live view; the type invariants of `LiveN`. -/
def SliceTolist : Prop :=
  ∀ (st : St) (self : Nat) (s : Slice) (n d : Int) (rest rs : List Int) (f : List Char) (c : Char),
    LiveN st self n d rest rs f → adjustFmt (st.mv self).view = .ok [c] → nativeChar c = true →
    (∀ x ∈ n :: rest, 0 ≤ x) → s.step ≠ some 0 →
    ∃ a b e L t t', sliceIndices s n = .ok (a, b, e) ∧ IsLen a b e L ∧
      memoryviewTolist self st = (.ok t, st) ∧
      let r := memorySubscript self (.one (.slice s none)) st
      r.1 = .ok (.view st.mvs.length) ∧ memoryviewTolist st.mvs.length r.2 = (.ok t', r.2) ∧
      t'.kids.length = L.toNat ∧
      (r.2.mv st.mvs.length).view.len = prod (L :: rest) * (st.mv self).view.itemsize ∧
      ∀ k : Nat, (k : Int) < L → t'.kids[k]? = t.kids[(a + k * e).toNat]?

theorem sliceTolist_proven : SliceTolist := by
  intro st self s n d rest rs f c hL hf hc hnn h0
  obtain ⟨a, b, e, L, h1, h2, hx⟩ := sliceItems_proven st self s n d rest rs f hL h0
  dsimp only at hx
  obtain ⟨g, hg⟩ := native_total st.mem c hc
  have hB := hL.base
  have hrank : (n :: rest).length = (st.mv self).view.ndim := by
    rcases hB.full.arrays with ⟨-, h4, -⟩ | ⟨sh, strs, hne, h4, -, h5, -⟩
    · rw [hL.shape] at h4
      cases h4
    · rw [hL.shape] at h5
      simp only [Option.some.injEq] at h5
      subst h5
      exact h4
  rcases hRR : memorySubscript self (.one (.slice s none)) st with ⟨res, S⟩
  rw [hRR] at hx
  simp only at hx
  obtain ⟨hr, hmem, hws, hwt, hwsome, hwn, hwl, hwf, hwsub, hwm, hwfl, hold, hrel, hk⟩ := hx
  subst hr
  obtain ⟨wst, hwst⟩ : ∃ l, (S.mv st.mvs.length).view.strides = some l := by
    cases hv : (S.mv st.mvs.length).view.strides with
    | none => rw [hv] at hwsome; cases hwsome
    | some l => exact ⟨l, rfl⟩
  have hg' : ∀ p, unpackRaw S.mem p [c] = .ok (g p) := by
    rw [hmem]
    exact hg
  have hlive : baseInaccessible S st.mvs.length = false := by
    have h3 : (S.mv st.mvs.length).flags.released = false := by rw [hwfl]; exact initFlags_released _
    have h4 : (S.mb (st.mv self).mbuf).released = false := by
      rw [hrel]
      have := hB.live
      simp only [baseInaccessible, Bool.or_eq_false_iff] at this
      exact this.2
    simp [baseInaccessible, h3, hwm, h4]
  have hfw : adjustFmt (S.mv st.mvs.length).view = .ok [c] := by
    rw [adjustFmt_format _ (st.mv self).view (by rw [hwf, hL.format])]
    exact hf
  have ht := memoryviewTolist_eq st self c (n :: rest) (d :: rs) g hB.live hf hg hL.shape hL.strides
    (by simp) hrank
  have ht' := memoryviewTolist_eq S st.mvs.length c (L :: rest) wst g hlive hfw hg' hws hwst (by simp)
    (by rw [hwn, ← hrank]; rfl)
  refine ⟨a, b, e, L, _, treeOf S.mem g (L :: rest) wst (S.mv st.mvs.length).view.suboffsets
    (S.mv st.mvs.length).view.buf, h1, h2, ht, ?_⟩
  dsimp only
  refine ⟨rfl, ht', ?_, by rw [hwl, initLen_prod], fun k hk' => ?_⟩
  · rw [treeOf_rows]
    simp only [List.length_map, walk_length]
  · obtain ⟨⟨h5, h6⟩, h7⟩ := hk k (by omega) hk'
    rw [hwst] at h7 hwt
    simp only [Option.getD_some] at h7 hwt
    have hL0 : 0 ≤ L := by
      have := h2.1
      omega
    rw [treeOf_rows, treeOf_rows, List.getElem?_map, List.getElem?_map,
      walk_getElem _ _ _ _ (by omega), walk_getElem _ _ _ _ (by omega)]
    simp only [Option.map_some, List.getD_cons_zero, List.drop_succ_cons, List.drop_zero, hwt, hwsub, hmem]
    rw [Int.toNat_of_nonneg h5, Int.mul_comm (wst.getD 0 0) (k : Int), h7]

/-- A 0-dim view: `m.tolist()` is one item and not a list, `m[()]` is that item, and it is the
native item at `buf` (`memoryview_tolist_impl`, :2248-2250, `memory_subscript`, :2592-2596).
Hypotheses: a live 0-dim view of a native format. -/
def ZeroDimItem : Prop :=
  ∀ (st : St) (self : Nat) (c : Char), baseInaccessible st self = false →
    adjustFmt (st.mv self).view = .ok [c] → nativeChar c = true → (st.mv self).view.ndim = 0 →
    ∃ x, unpackRaw st.mem (st.mv self).view.buf [c] = .ok x ∧
      memoryviewTolist self st = (.ok (.leaf x), st) ∧
      memorySubscript self (.tuple []) st = (.ok (.item x), st)

theorem zeroDimItem_proven : ZeroDimItem := by
  intro st self c hl hf hc h0
  obtain ⟨g, hg⟩ := native_total st.mem c hc
  refine ⟨g (st.mv self).view.buf, hg _, ?_, ?_⟩
  · simp only [memoryviewTolist, M.bind_app, checkReleased_ok _ _ hl, M.get, M.lift, hf, h0, ↓reduceIte,
      unpackSingle_live _ _ _ _ hl, hg, M.pure_app]
  · simp only [memorySubscript, M.bind_app, checkReleased_ok _ _ hl, M.get, h0, ↓reduceIte, M.lift, hf,
      unpackSingle_live _ _ _ _ hl, hg, M.pure_app]

/-- With flags that say "not C-contiguous", a view `PyBuffer_IsContiguous` calls C-contiguous is
empty: the two tests differ only where nothing is read. -/
theorem flags_contig_empty (v : Buf) (n d : Int) (hflag : (initFlags v).isC = false)
    (hc : pyBufferIsContiguous v 'C' = true)
    (h1 : v.ndim = 1 → v.shape = some [n] ∧ v.strides = some [d] ∧ 0 ≤ n ∧ v.len = n * v.itemsize) :
    v.len = 0 := by
  by_cases hl : v.len = 0
  · exact hl
  exfalso
  have hsb : v.suboffsets = none := by
    cases hs : v.suboffsets with
    | none => rfl
    | some l => simp [pyBufferIsContiguous, hs] at hc
  simp only [initFlags, hsb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Flags.isC] at hflag
  split at hflag
  · simp at hflag
  · rename_i hn
    obtain ⟨hsh, hst, hnn, hlen⟩ := h1 hn
    simp only [pyBufferIsContiguous, hsb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, isCContiguous,
      hl, hst, hsh, Option.getD_some, hn, cLoop, List.getD_cons_zero] at hc
    split at hflag
    · simp at hflag
    · rename_i hm
      simp only [mvContiguousNdim1, hsh, hst, Option.getD_some, List.getD_cons_zero, Bool.or_eq_true,
        beq_iff_eq, not_or] at hm
      have hn0 : n ≠ 0 := by
        intro e
        rw [e] at hlen
        exact hl (by simpa using hlen)
      have : n > 1 ∧ d ≠ v.itemsize := ⟨by omega, hm.2⟩
      simp [this] at hc
  · rename_i hn0 hn1
    simp only [hc, Bool.true_or] at hflag
    cases hflag

/-- `hash(m) == hash(m.tobytes())` for every read-only view of a byte format, of any number of
dimensions, strides and suboffsets (Doc/library/stdtypes.rst, `memoryview.__hash__`), and the value
stays: a later `hash` gives the same even after `release()`. The two read the memory by different
tests, `MV_C_CONTIGUOUS(flags)` (:3238) and `PyBuffer_IsContiguous` (:1063), and these differ only on an
empty view. Hypotheses: the conditions of the function itself (read-only, byte format, an exporter
whose `__hash__` succeeds and touches no view: the other cases are `HashHoldsExport` and
`HashViewExporter`), and the type invariants of the view, among them that a 0-dim view has no
suboffsets. -/
def HashIsTobytes : Prop :=
  ∀ (st : St) (self : Nat) (sh strs : List Int), Hashable st self →
    let v := (st.mv self).view
    (st.mv self).flags.isC = (initFlags v).isC → Full v → v.shape.getD [] = sh → v.strides.getD [] = strs →
    (v.ndim = 0 → v.suboffsets = none) → (∀ x ∈ sh, 0 ≤ x) → 0 < v.itemsize → v.len = prod sh * v.itemsize →
    (memoryHash self st).1 = (memoryviewTobytes self none st).1 ∧
    (∀ s', (s'.mv self).hash = ((memoryHash self st).2.mv self).hash →
      (memoryHash self s').1 = (memoryHash self st).1)

theorem fb_eq_copy (v : Buf) :
    { initSharedValues v v with
      shape := (initShapeStrides v).1, strides := (initShapeStrides v).2,
      suboffsets := initSuboffsets v } = viewCopy v := by
  unfold viewCopy
  cases initShapeStrides v
  rfl

theorem hashIsTobytes_proven : HashIsTobytes := by
  intro st self sh strs hH
  dsimp only
  intro hfl hfull hs1 hs2 h0 hnn hit hlen
  have hv := hH.valid
  have htob : ∀ b, pyBufferToContiguous st.mem (st.mv self).view (st.mv self).view.len 'C' = .ok b →
      (memoryviewTobytes self none st).1 = .ok b := by
    intro b hb
    simp only [memoryviewTobytes, M.bind_app, checkReleased_ok _ _ hH.live, M.pure_app, M.get, M.lift, hb,
      parseOrder]
  by_cases hC : (st.mv self).flags.isC = true
  · have hsb : (st.mv self).view.suboffsets = none := by
      by_cases hz : (st.mv self).view.ndim = 0
      · exact h0 hz
      · exact isC_no_subs _ (hfl ▸ hC) hz
    have hc := isC_contig _ (hfl ▸ hC) hsb
    have hp : pyBufferToContiguous st.mem (st.mv self).view (st.mv self).view.len 'C' =
        .ok (rdBytes st.mem (st.mv self).view.buf (st.mv self).view.len.toNat) := by
      simp [pyBufferToContiguous, hc]
    rw [htob _ hp, memoryHash_contig st self hH hC]
    refine ⟨rfl, fun s' hs => ?_⟩
    rw [St.mv_setMv _ _ _ hv] at hs
    exact hash_cached s' self _ hs
  · have hCf : (st.mv self).flags.isC = false := by simpa using hC
    have hz : (st.mv self).view.ndim ≠ 0 := by
      intro e
      rw [hfl] at hCf
      simp [initFlags, e, Flags.isC] at hCf
      split at hCf <;> simp_all
    obtain ⟨sh', strs', hne, hr1, hr2, h3, h4⟩ : ∃ a b, a ≠ [] ∧ a.length = (st.mv self).view.ndim ∧
        b.length = (st.mv self).view.ndim ∧ (st.mv self).view.shape = some a ∧
        (st.mv self).view.strides = some b := by
      rcases hfull.arrays with ⟨e, -, -⟩ | h
      · exact absurd e hz
      · exact h
    rw [h3] at hs1
    rw [h4] at hs2
    simp only [Option.getD_some] at hs1 hs2
    subst hs1 hs2
    have hb := tobytesC_proven st.mem (st.mv self).view sh' strs' h3 h4 hne hr1 hnn hit hlen
    have hF := flatBytes_length st.mem (st.mv self).view.itemsize (by omega) sh' strs'
      (st.mv self).view.suboffsets (st.mv self).view.buf hne hnn
    have hp : pyBufferToContiguous st.mem (st.mv self).view (st.mv self).view.len 'C' =
        .ok (flatBytes st.mem (st.mv self).view.itemsize sh' strs' (st.mv self).view.suboffsets
          (st.mv self).view.buf) := by
      by_cases hc : pyBufferIsContiguous (st.mv self).view 'C' = true
      · have h1 : (st.mv self).view.ndim = 1 →
            (st.mv self).view.shape = some [sh'.getD 0 0] ∧ (st.mv self).view.strides = some [strs'.getD 0 0] ∧
              0 ≤ sh'.getD 0 0 ∧ (st.mv self).view.len = sh'.getD 0 0 * (st.mv self).view.itemsize := by
          intro hn
          have l1 : sh'.length = 1 := by omega
          have l2 : strs'.length = 1 := by omega
          obtain ⟨n, rfl⟩ := List.length_eq_one_iff.1 l1
          obtain ⟨d, rfl⟩ := List.length_eq_one_iff.1 l2
          exact ⟨h3, h4, hnn n (by simp), by simpa [prod] using hlen⟩
        have h00 := flags_contig_empty _ _ _ (hfl ▸ hCf) hc h1
        have hnil : flatBytes st.mem (st.mv self).view.itemsize sh' strs' (st.mv self).view.suboffsets
            (st.mv self).view.buf = [] := by
          apply List.length_eq_zero_iff.1
          rw [hlen] at h00
          rw [h00] at hF
          omega
        simp [pyBufferToContiguous, hc, hnil, h00, rdBytes]
      · have hcf : pyBufferIsContiguous (st.mv self).view 'C' = false := by simpa using hc
        have hfb := (fb_eq_copy (st.mv self).view).trans (viewCopy_full _ hfull)
        rcases hi : initShapeStrides (st.mv self).view with ⟨a, b⟩
        rw [hi] at hfb
        simp only [pyBufferToContiguous, ne_eq, not_true_eq_false, ↓reduceIte, hcf, Bool.false_eq_true, hi]
        dsimp only at hfb ⊢
        rw [hfb]
        exact hb
    rw [htob _ hp, memoryHash_strided st self _ hH hCf hb]
    refine ⟨rfl, fun s' hs => ?_⟩
    rw [St.mv_setMv _ _ _ hv] at hs
    exact hash_cached s' self _ hs

/-- `memoryview.cast(format, shape)` from the arguments to the new view (`memoryview_cast_impl`,
:1447-1499, through `cast_to_1D` and `cast_to_ND`): a new view of the same buffer and byte size,
with `ndim == len(shape)`, the given shape, the new format and C strides, and `m` unchanged.
Hypotheses: what the function checks, each with its own refusal in `CastRejections`, `CastNDSpec`
and `Cast1DSpec`, and a live, C-contiguous source. -/
def CastShapeSpec : Prop :=
  ∀ (st : St) (self : Nat) (format : List Char) (c : Char) (size : Int) (fstr : List Char)
    (items : List Obj) (l : Int) (sh : List Int),
    self < st.mvs.length → (st.mv self).mbuf < st.mbufs.length →
    baseInaccessible st self = false → (st.mv self).flags.restricted = false →
    (st.mv self).flags.isC = true → ¬ HasZero (st.mv self).view →
    (∀ ch ∈ format, ch.toNat < 128) → getNativeFmtchar format = some (c, size) →
    getNativeFmtstr format = some fstr →
    (srcIsByte (st.mv self).view = true ∨ isByteFormat c = true) →
    (st.mv self).view.len.tmod size = 0 →
    0 < items.length → items.length ≤ 64 → ((st.mv self).view.ndim = 1 ∨ items.length = 1) →
    copyShape items size = .ok (l, sh) → (st.mv self).view.len = l →
    let r := memoryviewCast self format (some (.seq items)) st
    let n := st.mvs.length
    let v := (r.2.mv n).view
    r.1 = .ok n ∧ v.shape = some sh ∧ v.ndim = items.length ∧ v.strides = some (cStrides size sh) ∧
      v.format = some fstr ∧ v.itemsize = size ∧ v.len = (st.mv self).view.len ∧
      v.buf = (st.mv self).view.buf ∧ v.suboffsets = none ∧ (r.2.mv n).flags.isC = true ∧
      r.2.mem = st.mem ∧ (r.2.mv self).view = (st.mv self).view

theorem castShapeSpec_proven : CastShapeSpec := by
  intro st self format c size fstr items l sh hself hmb hrel hres hC hz hasc hf hs hbyte hmod hpos hmax hrank
    hcs hlen
  have hany := any_ascii_false format hasc
  have hz0 := zeroInShape_false _ hz
  have hgt : ¬ items.length > 64 := by omega
  have hne0 : items.length ≠ 0 := by omega
  have hlone : ((st.mv self).view.ndim != 1 && items.length != 1) = false := by
    rcases hrank with h | h <;> simp [h]
  dsimp only
  unfold memoryviewCast
  simp only [M.bind_app, checkReleased_ok _ _ hrel, checkRestricted_ok _ _ hres, M.get, hC, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, hz0, Bool.and_false, M.pure_app, hgt, hlone, hne0]
  have ⟨hr1, hA⟩ := mbufAddIncompleteView_added (st.mv self).mbuf (st.mv self).view items.length st
  rcases hrr : mbufAddIncompleteView (st.mv self).mbuf (some (st.mv self).view) items.length st with ⟨r1, st1⟩
  rw [hrr] at hr1 hA
  dsimp only at hr1 hA
  subst hr1
  have hview : (st1.mv st.mvs.length).view =
      initSharedValues { ndim := items.length } (st.mv self).view := by
    rw [hA.new]
  have hn : st.mvs.length < st1.mvs.length := by rw [hA.len]; omega
  have hc := castTo1D_spec st.mvs.length format st1 c size fstr hany hf hs
    (by rw [hview]; simpa [srcIsByte, initSharedValues] using hbyte)
    (by rw [hview]; simpa [initSharedValues] using hmod)
  rcases hs2 : castTo1D st.mvs.length format st1 with ⟨r2, s2⟩
  rw [hs2] at hc
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, hs2e⟩ := hc
  have hn2 : st.mvs.length < s2.mvs.length := by
    rw [hs2e]
    simpa [St.setMv] using hn
  have hmv2 : (s2.mv st.mvs.length).view =
      { (st1.mv st.mvs.length).view with
        format := some fstr, itemsize := size, ndim := 1,
        shape := some [Int.tdiv (st1.mv st.mvs.length).view.len size], strides := some [size],
        suboffsets := none } := by
    rw [hs2e, St.mv_setMv _ _ _ hn]
  have hit2 : (s2.mv st.mvs.length).view.itemsize = size := by rw [hmv2]
  have hlen2 : (s2.mv st.mvs.length).view.len = l := by
    rw [hmv2]
    show (st1.mv st.mvs.length).view.len = l
    rw [hview]
    exact hlen
  have hcn := castToND_ok st.mvs.length items items.length s2 l sh hne0 (by rw [hit2]; exact hcs) hlen2
  simp only [M.onError, M.bind_app, hs2, Option.isSome_some, ↓reduceIte, hcn, M.pure_app]
  have hshape := copyShape_ok _ _ _ _ hcs
  rw [St.mv_setMv _ _ _ hn2]
  dsimp only
  have hsub2 : (s2.mv st.mvs.length).view.suboffsets = none := by rw [hmv2]
  have hbuf2 : (s2.mv st.mvs.length).view.buf = (st.mv self).view.buf := by
    rw [hmv2]
    show (st1.mv st.mvs.length).view.buf = _
    rw [hview]
    rfl
  have hfmt2 : (s2.mv st.mvs.length).view.format = some fstr := by rw [hmv2]
  refine ⟨trivial, rfl, rfl, by rw [hit2], hfmt2, hit2, ?_, hbuf2, hsub2, ?_, ?_, ?_⟩
  · show (s2.mv st.mvs.length).view.len = _
    rw [hlen2, hlen]
  · exact initFlags_isC_of _ sh hsub2 rfl rfl (by simp only; omega) (by simp only; omega)
  · simp only [St.mem_setMv]
    rw [hs2e, St.mem_setMv]
    exact hA.mem
  · have hne : st.mvs.length ≠ self := by omega
    rw [St.mv_setMv_ne _ _ _ _ hne, hs2e, St.mv_setMv_ne _ _ _ _ hne, hA.old _ hself]

/-- `with m as x:` (`memory_enter`, `memory_exit`, :1182-1193): `__enter__` returns the view itself,
and a released view refuses; `__exit__` is `release`, so with no exports the view is released and
a second `__enter__` refuses. The refusal with exports is in `ReleaseRules`. Hypothesis: `i` exists. -/
def ContextRules : Prop :=
  ∀ (st : St) (i : Nat), i < st.mvs.length →
    (baseInaccessible st i = false → memoryEnter i st = (.ok i, st)) ∧
    ((st.mv i).exports = 0 → (memoryExit i st).1 = .ok () ∧
      ((memoryExit i st).2.mv i).flags.released = true ∧
      (memoryEnter i (memoryExit i st).2).1 = .error releasedError)

theorem contextRules_proven : ContextRules := by
  intro st i hv
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [memoryEnter, M.bind_app, checkReleased_ok _ _ h, M.pure_app]
  · have e : memoryExit i st = memoryRelease i st := by
      show memoryviewRelease i st = _
      simp only [memoryviewRelease, getExports, h, ↓reduceIte]
    have hr := memoryRelease_released i st hv
    rw [e]
    refine ⟨memoryRelease_ok i st, hr, ?_⟩
    simp only [memoryEnter, M.bind_app, checkReleased_err _ _ (released_inaccessible _ _ hr)]

/-- The exit of `PyMemoryView_GetContiguous` the function exists for, :998-1000: a read request in
C order on a view that is not contiguous gives a new view over a new `bytes` object, with C strides
and no suboffsets, holding the view's items in row-major order, and the temporary view is
dropped. `m` keeps its buffer. Hypotheses: a live view of any number of dimensions with
`len == product(shape) * itemsize`. -/
def GetContiguousCopy : Prop :=
  ∀ (st : St) (self : Nat) (sh strs : List Int) (f : List Char), LiveView st self →
    let v := (st.mv self).view
    v.shape = some sh → v.strides = some strs → v.format = some f → sh ≠ [] → (∀ x ∈ sh, 0 ≤ x) →
    0 < v.itemsize → v.len = prod sh * v.itemsize → pyBufferIsContiguous v 'C' = false →
    let r := memoryViewGetContiguous (.view self) false 'C' st
    let i := st.mvs.length + 1
    r.1 = .ok i ∧ (r.2.mv i).view.shape = some sh ∧ (r.2.mv i).view.format = some f ∧
      (r.2.mv i).view.strides = some (cStrides v.itemsize sh) ∧ (r.2.mv i).view.suboffsets = none ∧
      rdBytes r.2.mem st.mem.length v.len.toNat =
        flatBytes (st.mem ++ List.replicate v.len.toNat 0) v.itemsize sh strs v.suboffsets v.buf ∧
      (r.2.mv self).view = v

theorem getContiguousCopy_proven : GetContiguousCopy := by
  intro st self sh strs f hL
  dsimp only
  intro hsh hst hf hne hnn hit hlen hc
  have hview := viewCopy_full _ hL.full
  have hrank : sh.length = (st.mv self).view.ndim := by
    rcases hL.full.arrays with ⟨-, h4, -⟩ | ⟨a, b, -, h4, -, h5, -⟩
    · rw [hsh] at h4
      cases h4
    · rw [hsh] at h5
      simp only [Option.some.injEq] at h5
      subst h5
      exact h4
  have ⟨hr1, hA⟩ := mbufAddView_added (st.mv self).mbuf (st.mv self).view st hL.small
  rw [hview] at hA
  have e : memoryViewFromObject (.view self) st =
      mbufAddView (st.mv self).mbuf (some (st.mv self).view) st := by
    simp only [memoryViewFromObject, memoryViewFromObjectAndFlags, M.bind_app,
      checkReleased_ok _ _ hL.live, checkRestricted_ok _ _ hL.unres, M.get]
  rcases hrr : mbufAddView (st.mv self).mbuf (some (st.mv self).view) st with ⟨r1, st1⟩
  rw [hrr] at hr1 hA e
  simp only at hr1 hA
  subst hr1
  have hnew : (st1.mv st.mvs.length).view = (st.mv self).view := by rw [hA.new]
  have hcopy := fromContigCopy_proven st1 (st.mv self).view sh strs f hsh hst hf hne hrank hnn hit hlen
  dsimp only at hcopy
  rcases hrc : memoryFromContiguousCopy (st.mv self).view 'C' st1 with ⟨r2, s2⟩
  rw [hrc] at hcopy
  simp only at hcopy
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hcopy
  subst h1
  rcases hd : memoryDealloc st.mvs.length s2 with ⟨r3, s3⟩
  have hok := memoryDealloc_ok st.mvs.length s2
  rw [hd] at hok
  simp only at hok
  subst hok
  have hmono : Mono s2 s3 := by
    have h9 := deallocMono st.mvs.length s2
    rw [hd] at h9
    exact h9
  have hlen1 : st1.mvs.length = st.mvs.length + 1 := hA.len
  have hg : memoryViewGetContiguous (.view self) false 'C' st = (.ok (st.mvs.length + 1), s3) := by
    simp only [memoryViewGetContiguous, M.bind_app, e, M.get, hnew, Bool.false_and, Bool.false_eq_true,
      ↓reduceIte, hc, hrc, hd, M.pure_app, hlen1]
  rw [hg]
  simp only
  rw [hlen1] at h3 h4 h5 h6
  rw [hA.mem] at h7
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmono.view, h3]
  · rw [hmono.view, h4, hf]
  · rw [hmono.view, h5]
  · rw [hmono.view, h6]
  · rw [hmono.mem]
    exact h7
  · rw [hmono.view, h8 self (by rw [hlen1]; have := hL.valid; omega), hA.old _ hL.valid]

/-- `m[s] = x` on a 1-D writable view (`memory_ass_sub`, :2694-2719, through `init_slice` and
`copy_single`): for every slice with a non-zero step and every `x` of the same structure, item
`range(*s.indices(n))[k]` of `m` holds item `k` of `x`, also when the two overlap, and `x`'s buffer is
given back. Refusals are `SliceCleanup` and `CopySingleRefuses`. Hypotheses: a live, writable view with
no suboffsets, in the store; `x` of equal structure, with no suboffsets; the destination items do not
overlap each other, which a stride of at least `itemsize` gives. -/
def AssSliceSpec : Prop :=
  ∀ (st : St) (self : Nat) (n d : Int) (f fmt : List Char) (s : Slice),
    Live1D st self n d f → (st.mv self).view.suboffsets = none →
    adjustFmt (st.mv self).view = .ok fmt → (st.mv self).view.readonly = false → s.step ≠ some 0 →
    0 < (st.mv self).view.itemsize →
    let v := (st.mv self).view
    ∃ a b c L, sliceIndices s n = .ok (a, b, c) ∧ IsLen a b c L ∧
      ∀ (src : Buf) (ss : Int), src.ndim = 1 → src.shape = some [L] → src.strides = some [ss] →
        src.suboffsets = none → src.format = v.format → src.itemsize = v.itemsize →
        (L ≤ 1 ∨ v.itemsize ≤ d * c ∨ d * c ≤ -v.itemsize) →
        (∀ j : Nat, (j : Int) < L → 0 ≤ v.buf + d * (a + j * c) ∧
          v.buf + d * (a + j * c) + v.itemsize ≤ st.mem.length) →
        let r := memoryAssSub self (.one (.slice s none)) (some (.exporter (.val src) none)) st
        r.1 = .ok () ∧ ∀ k : Nat, (k : Int) < L →
          rdBytes r.2.mem (v.buf + d * (a + k * c)) v.itemsize.toNat =
            rdBytes st.mem (src.buf + k * ss) v.itemsize.toNat

theorem assSliceSpec_proven : AssSliceSpec := by
  intro st self n d f fmt s hL hsub hf hro h0 hit
  dsimp only
  obtain ⟨a, b, c, L, w, h1, h2, h3, hi, hws, ⟨wds, hwx⟩, hwn, hwi, hwf, hwsub, hwro, hdsc, hk⟩ :=
    initSlice_spec (st.mv self).view s n d [] [] hL.shape hL.strides hL.nonneg hL.bound hL.span h0
  refine ⟨a, b, c, L, h1, h2, fun src ss s1 s2 s3 s4 s5 s6 hover hbound => ?_⟩
  obtain ⟨dest, hdest⟩ : ∃ x : Buf, x = { w with len := (w.shape.getD []).getD 0 0 * w.itemsize } := ⟨_, rfl⟩
  have hdsh : dest.shape = some [L] := by rw [hdest]; exact hws
  have hdst : dest.strides = some [wds] := by rw [hdest]; exact hwx
  have hdn : dest.ndim = 1 := by rw [hdest]; show w.ndim = 1; rw [hwn, hL.ndim]
  have hdsb : dest.suboffsets = none := by rw [hdest]; show w.suboffsets = none; rw [hwsub, hsub]
  have hdit : dest.itemsize = (st.mv self).view.itemsize := by rw [hdest]; exact hwi
  have hdbuf : dest.buf = w.buf := by rw [hdest]
  have hdf : dest.format = src.format := by rw [hdest, s5]; exact hwf
  have heq : equivStructure dest src = .ok () :=
    equiv_self src dest [L] s2 (by rw [s1]; rfl) (by rw [hdsh, s2]) (by rw [hdn, s1]) hdf (by rw [hdit, s6])
  have hwds : ∀ j : Nat, (j : Int) < L → dest.buf + j * wds = (st.mv self).view.buf + d * (a + j * c) := by
    intro j hj
    have := (hk j (by omega) hj).2
    rw [hwx] at this
    rw [hdbuf]
    simpa using this
  have hspec := copySingleSpec_proven st self dest src L wds ss hL.live heq hdsh hdst s3 hdn s1 hdsb s4 h3
    (by rw [hdit]; exact hit)
    (by
      rw [hdit]
      by_cases hL1 : L ≤ 1
      · exact Or.inl hL1
      · have hw : wds = d * c := by
          have := hdsc wds (by rw [hwx]; rfl) (by omega)
          exact this
        rw [hw]
        rcases hover with h | h
        · exact absurd h hL1
        · exact Or.inr h)
    (by
      intro j hj
      rw [hwds j hj, hdit]
      exact hbound j hj)
  dsimp only at hspec
  rcases hcs : copySingle self dest src st with ⟨r1, s'⟩
  rw [hcs] at hspec
  simp only at hspec
  obtain ⟨h7, h8⟩ := hspec
  subst h7
  have hnd0 : ¬ (st.mv self).view.ndim = 0 := by rw [hL.ndim]; omega
  have hass : memoryAssSub self (.one (.slice s none)) (some (.exporter (.val src) none)) st =
      (.ok (), (pyBufferRelease src s').2) := by
    simp only [memoryAssSub, M.bind_app, checkReleased_ok _ _ hL.live, M.get, M.lift, hf, hro,
      Bool.false_eq_true, ↓reduceIte, hL.ndim, Nat.one_ne_zero, getBufferFull_val src st (by rw [s1]; omega),
      M.onError, sliceEvents_none s h0, hi, M.pure_app, ← hdest, hcs]
    have hok := pyBufferRelease_ok src s'
    rcases hrel : pyBufferRelease src s' with ⟨x, y⟩
    rw [hrel] at hok
    simp only at hok
    subst hok
    rfl
  rw [hass]
  refine ⟨rfl, fun k hk' => ?_⟩
  rw [(pyBufferRelease_mono src s').mem, ← hwds k hk']
  have := h8 k hk'
  rw [hdit] at this
  exact this

/-- `init_shape_strides`, :555-580, and `init_suboffsets`, :582-593: no arrays for 0 dimensions; a
missing shape or stride of a 1-D buffer rebuilt from `len` and `itemsize`; N-D arrays copied; and N-D
strides that are missing filled in by `init_strides_from_shape`, which is C order, as the buffer
protocol defines a NULL `strides`. Suboffsets are copied when there are any.
Hypotheses: the shape array has `ndim` entries. -/
def InitArrays : Prop :=
  ∀ (v : Buf),
    (v.ndim = 0 → initShapeStrides v = (none, none)) ∧
    (v.ndim = 1 → v.shape = none → v.strides = none →
      initShapeStrides v = (some [Int.tdiv v.len v.itemsize], some [v.itemsize])) ∧
    (∀ sh, v.shape = some sh → sh.length = v.ndim → 2 ≤ v.ndim →
      (v.strides = none → initShapeStrides v = (some sh, some (cStrides v.itemsize sh)) ∧
        isCContiguous { v with strides := some (cStrides v.itemsize sh) } = true) ∧
      (∀ l, v.strides = some l → l.length = v.ndim → initShapeStrides v = (some sh, some l))) ∧
    (∀ l, v.suboffsets = some l → l.length = v.ndim → initSuboffsets v = some l) ∧
    (v.suboffsets = none → initSuboffsets v = none)

theorem initArrays_proven : InitArrays := by
  intro v
  refine ⟨fun h => ?_, fun h1 h2 h3 => ?_, fun sh hs hl h2 => ⟨fun h3 => ⟨?_, ?_⟩, fun l h3 h4 => ?_⟩,
    fun l h1 h2 => ?_, fun h => ?_⟩
  · simp [initShapeStrides, h]
  · simp [initShapeStrides, h1, h2, h3]
  · have h0 : v.ndim ≠ 0 := by omega
    have h1 : v.ndim ≠ 1 := by omega
    simp only [initShapeStrides, h0, h1, ↓reduceIte, hs, Option.getD_some, h3]
    rw [← hl, List.take_length]
  · exact isCContiguous_cStrides _ sh hs rfl hl.symm
  · have h0 : v.ndim ≠ 0 := by omega
    have h1 : v.ndim ≠ 1 := by omega
    simp only [initShapeStrides, h0, h1, ↓reduceIte, hs, Option.getD_some, h3]
    rw [← hl, List.take_length, hl, ← h4, List.take_length]
  · simp [initSuboffsets, h1, List.take_of_length_le (show l.length ≤ v.ndim by omega)]
  · simp [initSuboffsets, h]

/-- `PyMemoryView_FromBuffer`, :769-794, on a `Py_buffer` with all its arrays, of any number of
dimensions: the view is that buffer with no exporter, and it is the only view of a new managed
buffer. A buffer that lacks them is `FromBufferReconstructs` and `InitArrays`. Hypotheses: the
arrays have `ndim` entries, at most 64. -/
def FromBufferFull : Prop :=
  ∀ (st : St) (info : Buf), Full info → info.ndim ≤ 64 →
    let r := memoryViewFromBuffer info false st
    let i := st.mvs.length
    let k := st.mbufs.length
    r.1 = .ok i ∧ (r.2.mv i).view = { info with obj := none } ∧ (r.2.mv i).mbuf = k ∧
      (r.2.mb k).exports = 1 ∧ r.2.mem = st.mem

theorem fromBufferFull_proven : FromBufferFull := by
  intro st info hfull hsmall
  obtain ⟨b, hb⟩ : ∃ b : Buf, b = { info with obj := none } := ⟨_, rfl⟩
  have hfb : Full b := by
    rw [hb]
    exact ⟨hfull.format, hfull.arrays, hfull.subs⟩
  have hview := viewCopy_full b hfb
  obtain ⟨st2, hst2⟩ : ∃ s2, s2 = let st1 : St := { st with mbufs := st.mbufs ++ [{}] }
      st1.setMb st.mbufs.length { st1.mb st.mbufs.length with master := b } := ⟨_, rfl⟩
  have hmb : st2.mb st.mbufs.length = { master := b } := by
    rw [hst2]
    exact fresh_mb st b
  have hlen : st2.mbufs.length = st.mbufs.length + 1 := by
    rw [hst2]
    simp [St.setMb]
  have e : memoryViewFromBuffer info false st = mbufAddView st.mbufs.length (some b) st2 := by
    have : memoryViewFromBuffer info false st = mbufAddView st.mbufs.length none st2 := by
      rw [hst2, hb]
      rfl
    rw [this, mbufAddView_none, hmb]
  have ⟨h2, hA⟩ := mbufAddView_added st.mbufs.length b st2 (by rw [hb]; exact hsmall)
  rw [hview] at hA
  have hmv : st2.mvs.length = st.mvs.length := by rw [hst2]; rfl
  have hmem : st2.mem = st.mem := by rw [hst2]; rfl
  rw [hmv] at h2
  have hnew : ((mbufAddView st.mbufs.length (some b) st2).2.mv st.mvs.length) =
      { mbuf := st.mbufs.length, view := b, flags := initFlags b } := by
    have := hA.new
    rwa [hmv] at this
  dsimp only
  rw [e, hnew]
  refine ⟨h2, by rw [hb], rfl, ?_, ?_⟩
  · rw [hA.exports (by omega), hmb]
    rfl
  · rw [hA.mem, hmem]

/-- `memoryview._from_flags(x, flags)`, :1031-1036, gives `flags` to an exporter
(`_PyManagedBuffer_FromObject`, :88-104): a writable request on a read-only exporter is refused
with no view made, and without `PyBUF_FORMAT` the master has no format and the view reads `B`,
as `init_shared_values` fills it in (:550). Hypotheses: the case; at most 64 dimensions. -/
def FromFlagsExporter : Prop :=
  ∀ (st : St) (b : Buf) (flags : Nat), b.ndim ≤ 64 →
    (req flags bufWritable = true → b.readonly = true →
      (memoryviewFromFlags (.exporter (.val b) none) flags st).1 =
        .error (bufferError "Object is not writable.")) ∧
    (req flags bufWritable = false → req flags bufFormat = false →
      let r := memoryviewFromFlags (.exporter (.val b) none) flags st
      let i := st.mvs.length
      r.1 = .ok i ∧ (r.2.mb st.mbufs.length).master.format = none ∧
        (r.2.mv i).view.format = some ['B'] ∧ (r.2.mv i).view.buf = b.buf ∧ (r.2.mv i).view.len = b.len)

theorem fromFlagsExporter_proven : FromFlagsExporter := by
  intro st b flags hsmall
  constructor
  · intro h1 h2
    have hg : simpleGetbuffer b flags = .error (bufferError "Object is not writable.") := by
      simp [simpleGetbuffer, h1, h2]
    simp only [memoryviewFromFlags, memoryViewFromObjectAndFlags, M.bind_app, fire, M.pure_app, viewOfExporter,
      managedBufferFromObject, mbufAlloc, M.lift, hg, Ret.get_val]
  · intro h1 h2
    obtain ⟨m, hg, hmf, hmn, hmb, hml⟩ : ∃ m, simpleGetbuffer b flags = .ok m ∧ m.format = none ∧
        m.ndim = b.ndim ∧ m.buf = b.buf ∧ m.len = b.len := by
      refine ⟨{ b with
        format := if req flags bufFormat then b.format else none,
        shape := if req flags bufND then b.shape else none,
        strides := if req flags bufStrides then b.strides else none,
        suboffsets := if req flags bufIndirect then b.suboffsets else none }, ?_, ?_, rfl, rfl, rfl⟩
      · simp [simpleGetbuffer, h1]
      · simp [h2]
    obtain ⟨st2, hst2⟩ : ∃ s2, s2 = let st1 : St := { st with mbufs := st.mbufs ++ [{}] }
        st1.setMb st.mbufs.length { st1.mb st.mbufs.length with master := m } := ⟨_, rfl⟩
    have hmbk : st2.mb st.mbufs.length = { master := m } := by
      rw [hst2]
      exact fresh_mb st m
    have hlen : st2.mbufs.length = st.mbufs.length + 1 := by
      rw [hst2]
      simp [St.setMb]
    have hsm : m.ndim ≤ 64 := by omega
    have hn : mbufAddView st.mbufs.length none st2 = mbufAddView st.mbufs.length (some m) st2 := by
      rw [mbufAddView_none, hmbk]
    have ⟨h3, hA⟩ := mbufAddView_added st.mbufs.length m st2 hsm
    have e : memoryviewFromFlags (.exporter (.val b) none) flags st = mbufAddView st.mbufs.length (some m) st2 := by
      simp only [memoryviewFromFlags, memoryViewFromObjectAndFlags, M.bind_app, fire, M.pure_app, viewOfExporter,
        managedBufferFromObject, mbufAlloc, M.lift, hg, M.modify, Ret.get_val]
      rw [← hst2]
      simp only [M.onError, hn]
      rcases hrr : mbufAddView st.mbufs.length (some m) st2 with ⟨r, s⟩
      rw [hrr] at h3
      simp only at h3
      subst h3
      rfl
    have hmv : st2.mvs.length = st.mvs.length := by rw [hst2]; rfl
    rw [hmv] at h3
    have hnew : ((mbufAddView st.mbufs.length (some m) st2).2.mv st.mvs.length).view = viewCopy m := by
      have := hA.new
      rw [hmv] at this
      rw [this]
    dsimp only
    rw [e, hnew]
    have hvc : (viewCopy m).format = some ['B'] ∧ (viewCopy m).buf = m.buf ∧ (viewCopy m).len = m.len := by
      unfold viewCopy
      cases initShapeStrides m
      simp [initSharedValues, hmf]
    refine ⟨h3, ?_, hvc.1, by rw [hvc.2.1, hmb], by rw [hvc.2.2, hml]⟩
    rw [hA.master (by omega), hmbk]
    exact hmf

/-- `_PyMemoryView_FromBufferProc`, :831-848, for every buffer proc. A proc that fails passes its
exception up and releases nothing; a proc that succeeds with a usable buffer gives a new view of it
on a new managed buffer; a buffer `mbuf_add_view` refuses is released. Hypotheses: the case. -/
def BufferProcRules : Prop :=
  ∀ (st : St) (proc : M Buf),
    let s0 : St := { st with mbufs := st.mbufs ++ [{}] }
    let k := st.mbufs.length
    (∀ e s, proc s0 = (.error e, s) → bufferProc proc st = (.error e, s)) ∧
    (∀ b s, proc s0 = (.ok b, s) → Full b → b.ndim ≤ 64 → k < s.mbufs.length →
      let r := bufferProc proc st
      r.1 = .ok s.mvs.length ∧ (r.2.mv s.mvs.length).view = b ∧ (r.2.mv s.mvs.length).mbuf = k) ∧
    (∀ b s, proc s0 = (.ok b, s) → 64 < b.ndim → k < s.mbufs.length →
      let r := bufferProc proc st
      r.1 = .error (.valueError "memoryview: number of dimensions must not exceed 64") ∧
        (r.2.mb k).released = true)

theorem bufferProcRules_proven : BufferProcRules := by
  intro st proc s0 k
  have hal : (mbufAlloc st) = (.ok k, s0) := rfl
  refine ⟨fun e s h => ?_, fun b s h hf hs hk => ?_, fun b s h hn hk => ?_⟩
  · simp only [bufferProc, M.bind_app, hal, h]
  · have hm := St.mb_setMb s k { s.mb k with master := b } hk
    generalize hS : s.setMb k { s.mb k with master := b } = s2 at hm
    have hadd : mbufAddView k none s2 = mbufAddView k (some b) s2 := by rw [mbufAddView_none, hm]
    have ⟨h2, hA⟩ := mbufAddView_added k b s2 hs
    rw [viewCopy_full b hf] at hA
    have hlen : s2.mvs.length = s.mvs.length := by rw [← hS]; rfl
    rw [hlen] at h2
    have e : bufferProc proc st = mbufAddView k (some b) s2 := by
      simp only [bufferProc, M.bind_app, hal, h, M.modify, M.pure_app, hS, M.onError, hadd]
      rcases hrr : mbufAddView k (some b) s2 with ⟨r, s'⟩
      rw [hrr] at h2
      simp only at h2
      subst h2
      rfl
    have hnew := hA.new
    rw [hlen] at hnew
    dsimp only
    rw [e, hnew]
    exact ⟨h2, rfl, rfl⟩
  · have hm := St.mb_setMb s k { s.mb k with master := b } hk
    generalize hS : s.setMb k { s.mb k with master := b } = s2 at hm
    have hk2 : k < s2.mbufs.length := by
      rw [← hS]
      simpa [St.setMb] using hk
    have hadd : mbufAddView k none s2 =
        (.error (.valueError "memoryview: number of dimensions must not exceed 64"), s2) := by
      simp only [mbufAddView, M.bind_app, M.get, Option.getD_none, hm]
      rw [if_pos hn]
      rfl
    have e : bufferProc proc st =
        (.error (.valueError "memoryview: number of dimensions must not exceed 64"), (mbufDealloc k s2).2) := by
      simp only [bufferProc, M.bind_app, hal, h, M.modify, M.pure_app, hS, M.onError, hadd]
    dsimp only
    rw [e]
    refine ⟨rfl, ?_⟩
    simp only [mbufDealloc, mbufRelease]
    split
    · assumption
    · apply (pyBufferRelease_mono _ _).mb
      rw [St.mb_setMb _ _ _ hk2]

/-- `memoryview_cast_impl`, :1496-1498: when a cast fails after the new view is made, `Py_DECREF(mv)`
gives its export of the managed buffer back. Hypotheses: a live, C-contiguous source that passes the
first checks; a format that is not native, the case; the buffer counts `self`, a type invariant. -/
def CastCleanup : Prop :=
  ∀ (st : St) (self : Nat) (format : List Char),
    self < st.mvs.length → (st.mv self).mbuf < st.mbufs.length →
    baseInaccessible st self = false → (st.mv self).flags.restricted = false →
    (st.mv self).flags.isC = true → ((st.mv self).view.ndim = 1 ∨ ¬ HasZero (st.mv self).view) →
    (∀ ch ∈ format, ch.toNat < 128) → getNativeFmtchar format = none →
    (st.mb (st.mv self).mbuf).exports ≠ 0 →
    let r := memoryviewCast self format none st
    (∃ e, r.1 = .error e) ∧ (r.2.mb (st.mv self).mbuf).exports = (st.mb (st.mv self).mbuf).exports

theorem castCleanup_proven : CastCleanup := by
  intro st self format hself hmb hrel hres hC hz hasc hf hne
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
  have hnew := hA.new
  have hmbuf : (st1.mv st.mvs.length).mbuf = (st.mv self).mbuf := by rw [hnew]
  have hc1 : castTo1D st.mvs.length format st1 =
      (.error (.valueError "memoryview: destination format must be a native single character format prefixed with an optional '@'"), st1) := by
    unfold castTo1D
    simp only [M.bind_app, M.get, hany, Bool.false_eq_true, ↓reduceIte, hf, M.throw_app]
  simp only [M.onError, M.bind_app, hc1]
  have hdeal : memoryDealloc st.mvs.length st1 = memoryRelease st.mvs.length st1 := by
    unfold memoryDealloc
    rw [hnew]
  have hx := memoryRelease_exports st1 st.mvs.length (by rw [hnew])
    (by rw [hmbuf, hA.exports hmb]; omega) (by rw [hmbuf, hA.mbufs]; exact hmb)
  rw [hmbuf, hA.exports hmb] at hx
  refine ⟨⟨_, rfl⟩, ?_⟩
  rw [hdeal, hx]
  omega

end PyLean.BytesObj.Mem
