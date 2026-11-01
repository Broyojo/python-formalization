import PyLean.BytesObj.Mem.Tuple

/-!
`PyMemoryView_GetContiguous`, `memory_from_contiguous_copy`, `copy_single`, and the struct
path of comparison on a format `struct` rejects.
-/

namespace PyLean.BytesObj.Mem

open PyLean

/-- A format `struct` rejects compares unequal, with no exception (`fix_struct_error_int`,
:2916-2928, reached at :3152-3160): "StructError: invalid or unknown format -> not equal".
Hypotheses: the shapes are equivalent, or the earlier exit is taken; the format is not native. -/
def CmpBadFormat : Prop :=
  ∀ (m : Mem) (vv ww : Buf) (msg : String),
    equivShape vv ww = true → getNativeFmtchar (vv.format.getD []) = none →
    structGetUnpacker (vv.format.getD []) vv.itemsize = .error (structError msg) →
    compareBufs m vv ww = .ok false

theorem cmpBadFormat_proven : CmpBadFormat := by
  intro m vv ww msg h1 h2 h3
  simp only [compareBufs, h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h2, true_or, h3]
  rfl

/-- `dest[k] = src[k]` for all `k` after `m[s] = src` on a 1-D view with no suboffsets, by
`copy_single`, through either branch of `copy_base`: the bytes are those the source held
before the copy, also when the two views overlap (`memmove` semantics, and the scratch buffer
in the strided branch). Hypotheses: `equiv_structure` passed (the function checks it) and
either both strides are `itemsize` or the destination items do not overlap each other. -/
def CopySingleSpec : Prop :=
  ∀ (st : St) (self : Nat) (dest src : Buf) (n ds ss : Int),
    baseInaccessible st self = false → equivStructure dest src = .ok () →
    dest.shape = some [n] → dest.strides = some [ds] → src.strides = some [ss] → dest.ndim = 1 →
    src.ndim = 1 → dest.suboffsets = none → src.suboffsets = none → 0 ≤ n → 0 < dest.itemsize →
    (dest.itemsize ≤ ds ∨ ds ≤ -dest.itemsize) →
    (∀ j : Nat, (j : Int) < n → 0 ≤ dest.buf + j * ds ∧ dest.buf + j * ds + dest.itemsize ≤ st.mem.length) →
    let r := copySingle self dest src st
    r.1 = .ok () ∧ ∀ k : Nat, (k : Int) < n →
      rdBytes r.2.mem (dest.buf + k * ds) dest.itemsize.toNat =
        rdBytes st.mem (src.buf + k * ss) dest.itemsize.toNat

theorem rdBytes_contig_item (sm dm : Mem) (it n : Nat) (dptr sptr : Int) (k : Nat) (hk : k < n)
    (hd : 0 ≤ dptr) (hb : dptr + (n * it : Nat) ≤ dm.length) :
    rdBytes (wrBytes dm dptr (rdBytes sm sptr (n * it))) (dptr + (k * it : Nat)) it =
      rdBytes sm (sptr + (k * it : Nat)) it := by
  obtain ⟨c, hc⟩ : ∃ c, n = k + 1 + c := ⟨n - k - 1, by omega⟩
  have hsplit : n * it = k * it + (it + c * it) := by
    subst hc
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
    omega
  rw [hsplit, rdBytes_append, rdBytes_append, ← wrBytes_append]
  simp only [rdBytes_length]
  rw [← wrBytes_append]
  simp only [rdBytes_length]
  rw [rdBytes_out _ _ _ _ _ (by omega) (by omega) (by simp [rdBytes_length]; try omega)]
  have h := rdBytes_wrBytes (wrBytes dm dptr (rdBytes sm sptr (k * it))) (dptr + (k * it : Nat))
    (rdBytes sm (sptr + (k * it : Nat)) it) (by omega) (by
      rw [wrBytes_length, rdBytes_length]
      have : (n * it : Nat) = k * it + (it + c * it) := hsplit
      have e : ((n * it : Nat) : Int) = ((k * it : Nat) : Int) + ((it + c * it : Nat) : Int) := by
        rw [this]; rfl
      omega)
  rw [rdBytes_length] at h
  exact h

theorem copySingleSpec_proven : CopySingleSpec := by
  intro st self dest src n ds ss hl he hsh hst hsst hd1 hs1 hdsub hssub hn hit hds hb
  have hitn : ((dest.itemsize.toNat : Nat) : Int) = dest.itemsize := Int.toNat_of_nonneg (by omega)
  have hc : copySingle self dest src st =
      (.ok (), { st with
        mem := copyBase n dest.itemsize dest.buf ds none src.buf ss none
          (!lastDimIsContiguous dest src) st.mem st.mem }) := by
    simp only [copySingle, M.bind_app, checkReleased_ok _ _ hl, M.lift, he, M.get, hsh, hst, hsst, hdsub,
      hssub, Option.getD_some, List.getD_cons_zero, M.modify]
  dsimp only
  rw [hc]
  refine ⟨rfl, ?_⟩
  intro k hk
  dsimp only
  cases hu : (!lastDimIsContiguous dest src) with
  | true =>
    exact copyStrided_proven st.mem st.mem n dest.itemsize dest.buf src.buf ds ss hn hit hds hb k hk
  | false =>
    have hlast : lastDimIsContiguous dest src = true := by simpa using hu
    simp only [lastDimIsContiguous, Bool.and_eq_true, beq_iff_eq, hd1, hs1, hst, hsst, Option.getD_some]
      at hlast
    obtain ⟨⟨-, h1⟩, h2⟩ := hlast
    have hds' : ds = dest.itemsize := by simpa using h1
    have hss' : ss = src.itemsize := by simpa using h2
    have hsame : src.itemsize = dest.itemsize := by
      simp only [equivStructure] at he
      split at he
      · simp at he
      · rename_i hx
        simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hx
        simp only [equivFormat, Bool.and_eq_true, beq_iff_eq] at hx
        exact hx.1.2.symm
    subst hds'
    rw [hsame] at hss'
    subst hss'
    simp only [copyBase, Bool.not_false, ↓reduceIte]
    obtain ⟨it, hit'⟩ : ∃ it : Nat, dest.itemsize = (it : Int) := ⟨dest.itemsize.toNat, hitn.symm⟩
    obtain ⟨nn, hnn⟩ : ∃ m : Nat, n = (m : Int) := ⟨n.toNat, (Int.toNat_of_nonneg hn).symm⟩
    subst hnn
    have hkk : k < nn := by omega
    rw [hit']
    have e1 : (((nn : Int) * (it : Int)).toNat) = nn * it := by
      rw [← Int.natCast_mul, Int.toNat_natCast]
    have e2 : ((it : Int)).toNat = it := Int.toNat_natCast _
    rw [e1, e2]
    have hit0 : 0 < it := by omega
    have hb0 := hb 0 (by omega)
    have hb1 : dest.buf + ((nn * it : Nat) : Int) ≤ st.mem.length := by
      have hl' := hb (nn - 1) (by omega)
      rw [hit'] at hl'
      have : ((nn - 1 : Nat) : Int) * (it : Int) + (it : Int) = ((nn * it : Nat) : Int) := by
        obtain ⟨c, rfl⟩ : ∃ c, nn = c + 1 := ⟨nn - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        rw [Nat.add_mul, Nat.one_mul]
        push_cast
        rfl
      omega
    have h := rdBytes_contig_item st.mem st.mem it nn dest.buf src.buf k hkk (by simpa using hb0.1) hb1
    simpa [Int.natCast_mul] using h

theorem mbufRelease_ok (k : Nat) (st : St) : (mbufRelease k st).1 = .ok () := by
  unfold mbufRelease
  dsimp only
  split
  · rfl
  · exact pyBufferRelease_ok _ _

theorem memoryRelease_ok (i : Nat) (st : St) : (memoryRelease i st).1 = .ok () := by
  unfold memoryRelease
  dsimp only
  split
  · rfl
  · split
    · exact mbufRelease_ok _ _
    · rfl

theorem memoryDealloc_ok (i : Nat) (st : St) : (memoryDealloc i st).1 = .ok () := by
  have h := memoryRelease_ok i st
  unfold memoryDealloc
  dsimp only
  rcases hr : memoryRelease i st with ⟨r, s⟩
  rw [hr] at h
  simp only at h
  subst h
  dsimp only
  split
  · split
    · exact memoryRelease_ok _ _
    · rfl
  · rfl

/-- `PyMemoryView_GetContiguous` for a 1-D source (:965-1001): a write request on a read-only
view and a write request on a non-contiguous view raise `BufferError`, and a view already
contiguous in the requested order comes back on the same memory.
Hypotheses: a live, unrestricted view. -/
def GetContiguousRules : Prop :=
  ∀ (st : St) (self : Nat) (n d : Int) (f : List Char) (order : Char),
    Live1D st self n d f →
    let v := (st.mv self).view
    (v.readonly = true →
      (memoryViewGetContiguous (.view self) true order st).1 =
        .error (bufferError "underlying buffer is not writable")) ∧
    (pyBufferIsContiguous v order = true →
      ∀ w, (w = true → v.readonly = false) →
      let r := memoryViewGetContiguous (.view self) w order st
      r.1 = .ok st.mvs.length ∧ (r.2.mv st.mvs.length).view = v ∧ r.2.mem = st.mem) ∧
    (pyBufferIsContiguous v order = false → v.readonly = false →
      (memoryViewGetContiguous (.view self) true order st).1 =
        .error (bufferError "writable contiguous buffer requested for a non-contiguous object."))

theorem getContiguousRules_proven : GetContiguousRules := by
  intro st self n d f order hL
  have hview := viewCopy_1d _ n d f hL.ndim hL.shape hL.strides hL.subs hL.format
  have ⟨hr1, hA⟩ := mbufAddView_added (st.mv self).mbuf (st.mv self).view st (by rw [hL.ndim]; omega)
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
  have hdeal : ∀ s, (memoryDealloc st.mvs.length s).1 = .ok () := fun s => memoryDealloc_ok _ _
  have thrown : ∀ (s : St) (x : PyExc),
      ((memoryDealloc st.mvs.length >>= fun _ => (throw x : M Nat)) s).1 = .error x := by
    intro s x
    rw [M.bind_app]
    have := hdeal s
    rcases hd : memoryDealloc st.mvs.length s with ⟨rd, sd⟩
    rw [hd] at this
    simp only at this
    subst this
    rfl
  dsimp only
  refine ⟨fun hro => ?_, fun hc w hw => ?_, fun hc hro => ?_⟩
  · simp only [memoryViewGetContiguous, M.bind_app, e, M.get, hnew, hro, Bool.and_self, ↓reduceIte]
    exact thrown _ _
  · have hw' : (w && (st.mv self).view.readonly) = false := by
      cases w with
      | false => rfl
      | true => simp [hw rfl]
    simp only [memoryViewGetContiguous, M.bind_app, e, M.get, hnew, hw', Bool.false_eq_true, ↓reduceIte,
      hc, M.pure_app]
    exact ⟨trivial, trivial, hA.mem⟩
  · simp only [memoryViewGetContiguous, M.bind_app, e, M.get, hnew, hro, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, hc]
    exact thrown _ _

/-- `memory_from_contiguous_copy` in order `'C'` for a view with full information (:888-946,
reached by `PyMemoryView_GetContiguous` for a read request on a non-contiguous view): a new
view over a new bytes object, with the shape and format of the source (`mbuf_copy_format`), C
strides and no suboffsets, holding the source's items in row-major order. `tolist(input) ==
tolist(output)`, as the comment at :950-953 says. `m` is the store including the new bytes.
Hypotheses: the type invariants of a buffer. -/
def FromContigCopy : Prop :=
  ∀ (st : St) (src : Buf) (sh strs : List Int) (f : List Char), src.shape = some sh →
    src.strides = some strs → src.format = some f →
    sh ≠ [] → sh.length = src.ndim → (∀ x ∈ sh, 0 ≤ x) → 0 < src.itemsize →
    src.len = prod sh * src.itemsize →
    let base : Int := st.mem.length
    let m := st.mem ++ List.replicate src.len.toNat 0
    let r := memoryFromContiguousCopy src 'C' st
    let i := st.mvs.length
    let v := (r.2.mv i).view
    r.1 = .ok i ∧ v.buf = base ∧ v.shape = some sh ∧ v.format = src.format ∧
      v.strides = some (cStrides src.itemsize sh) ∧ v.suboffsets = none ∧
      rdBytes r.2.mem base src.len.toNat = flatBytes m src.itemsize sh strs src.suboffsets src.buf

theorem simple_full (e : Buf) (h : e.suboffsets = none) : simpleGetbuffer e bufFullRO = .ok e := by
  have h1 : req bufFullRO bufWritable = false := by decide
  have h2 : req bufFullRO bufFormat = true := by decide
  have h3 : req bufFullRO bufND = true := by decide
  have h4 : req bufFullRO bufStrides = true := by decide
  have h5 : req bufFullRO bufIndirect = true := by decide
  simp only [simpleGetbuffer, h1, h2, h3, h4, h5, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- What `contigBytes` leaves. -/
structure Bytes (st s : St) (src : Buf) (k : Nat) : Prop where
  mem : s.mem = st.mem ++ List.replicate src.len.toNat 0
  mvs : s.mvs = st.mvs
  valid : k < s.mbufs.length
  buf : (s.mb k).master.buf = st.mem.length
  len : (s.mb k).master.len = src.len.toNat
  format : (s.mb k).master.format = src.format
  obj : (s.mb k).master.obj = some (.exp 1000000)

/-- The buffer of the new bytes object. -/
def zeroBuf (st : St) (src : Buf) : Buf :=
  { obj := some (.exp 1000000), buf := st.mem.length,
    len := (List.replicate src.len.toNat 0).length, itemsize := 1, readonly := true, ndim := 1,
    format := some ['B'], shape := some [(List.replicate src.len.toNat 0).length],
    strides := some [1] }

theorem contigBytes_spec (st : St) (src : Buf) :
    (contigBytes src st).1 = .ok st.mbufs.length ∧
    Bytes st (contigBytes src st).2 src st.mbufs.length := by
  obtain ⟨e, he⟩ : ∃ e : Buf, e = zeroBuf st src := ⟨_, rfl⟩
  obtain ⟨s0, hs0⟩ : ∃ s : St, s = { st with mem := st.mem ++ List.replicate src.len.toNat 0 } := ⟨_, rfl⟩
  have hse : e.suboffsets = none := by rw [he]; rfl
  have hk : s0.mbufs.length = st.mbufs.length := by rw [hs0]
  have hb : bytesBuf (List.replicate src.len.toNat 0) st = (.ok e, s0) := by rw [he, hs0]; rfl
  obtain ⟨s2, hs2⟩ : ∃ s2, s2 = let s1 : St := { s0 with mbufs := s0.mbufs ++ [{}] }
      s1.setMb s0.mbufs.length { s1.mb s0.mbufs.length with master := e } := ⟨_, rfl⟩
  have hmb2 : s2.mb s0.mbufs.length = { master := e } := by rw [hs2]; exact fresh_mb s0 e
  have hm : managedBufferFromObject e bufFullRO s0 = (.ok s0.mbufs.length, s2) := by
    simp only [managedBufferFromObject, M.bind_app, mbufAlloc, M.lift, simple_full e hse, M.modify,
      M.pure_app]
    rw [hs2]
  have hlen2 : s0.mbufs.length < s2.mbufs.length := by rw [hs2]; simp [St.setMb]
  have hc : contigBytes src st = (.ok s0.mbufs.length, s2.setMb s0.mbufs.length
      { s2.mb s0.mbufs.length with
        master := { (s2.mb s0.mbufs.length).master with format := src.format } }) := by
    simp only [contigBytes, M.bind_app, hb, hm, M.modify, M.pure_app]
  have hm3 := St.mb_setMb s2 s0.mbufs.length { s2.mb s0.mbufs.length with
    master := { (s2.mb s0.mbufs.length).master with format := src.format } } hlen2
  rw [hmb2] at hm3
  rw [hc, hk] at *
  have hmem : s2.mem = st.mem ++ List.replicate src.len.toNat 0 := by rw [hs2, hs0]; rfl
  have hmvs : s2.mvs = st.mvs := by rw [hs2, hs0]; rfl
  refine ⟨rfl, hmem, hmvs, by simpa [St.setMb] using hlen2, ?_, ?_, ?_, ?_⟩
  all_goals simp only [hmb2]
  all_goals rw [hm3]
  all_goals rw [he]
  all_goals try rfl
  all_goals simp [zeroBuf]

theorem fromContigCopy_proven : FromContigCopy := by
  intro st src sh strs f hsh hst hf hne hn hnn hit hlen
  dsimp only
  have ⟨h1, hB⟩ := contigBytes_spec st src
  simp only [memoryFromContiguousCopy, M.bind_app]
  rcases hrr : contigBytes src st with ⟨r, s⟩
  rw [hrr] at h1 hB
  simp only at h1 hB
  subst h1
  simp only
  have ⟨ha, hA⟩ := mbufAddIncompleteView_added st.mbufs.length (s.mb st.mbufs.length).master src.ndim s
  have e0 : mbufAddIncompleteView st.mbufs.length none src.ndim s =
      mbufAddIncompleteView st.mbufs.length (some (s.mb st.mbufs.length).master) src.ndim s := rfl
  unfold contigFill
  simp only [M.bind_app, e0]
  rcases hr2 : mbufAddIncompleteView st.mbufs.length (some (s.mb st.mbufs.length).master) src.ndim s with
    ⟨r2, s3⟩
  rw [hr2] at ha hA
  simp only at ha hA
  subst ha
  have hmvs : s.mvs.length = st.mvs.length := by rw [hB.mvs]
  have hx : (s3.mv st.mvs.length).view =
      initSharedValues { ndim := src.ndim } (s.mb st.mbufs.length).master := by
    have := hA.new
    rw [hmvs] at this
    rw [this]
  have hmem3 : s3.mem = st.mem ++ List.replicate src.len.toNat 0 := by rw [hA.mem, hB.mem]
  have hlenN : (0 : Int) ≤ src.len := by
    rw [hlen]
    exact Int.mul_nonneg (prod_nonneg _ hnn) (by omega)
  obtain ⟨dest, hdest⟩ : ∃ d : Buf, d =
      { (s3.mv st.mvs.length).view with
        itemsize := src.itemsize, shape := some sh, strides := some (cStrides src.itemsize sh),
        suboffsets := none } := ⟨_, rfl⟩
  have hd : dest =
      { obj := some (.exp 1000000), buf := st.mem.length, len := src.len,
        itemsize := src.itemsize, readonly := (s.mb st.mbufs.length).master.readonly, ndim := src.ndim,
        format := some f, shape := some sh, strides := some (cStrides src.itemsize sh),
        suboffsets := none, hook := (s.mb st.mbufs.length).master.hook } := by
    rw [hdest, hx]
    simp [initSharedValues, hB.buf, hB.len, hB.format, hB.obj, hf, Int.toNat_of_nonneg hlenN]
  have hequiv := equiv_self src dest sh hsh hn (by rw [hd, hsh]) (by rw [hd]) (by rw [hd, hf]) (by rw [hd])
  have hdn : dest.ndim = src.ndim := by rw [hd]
  have hn3 : st.mvs.length < s3.mvs.length := by rw [hA.len]; omega
  have hl := flatBytes_length (st.mem ++ List.replicate src.len.toNat 0) src.itemsize (by omega) sh strs
    src.suboffsets src.buf hne hnn
  have hc := copyRec_spec src.itemsize (by omega) (!lastDimIsContiguous dest src)
    (st.mem ++ List.replicate src.len.toNat 0) sh hne hnn st.mem.length src.buf strs src.suboffsets
    (st.mem ++ List.replicate src.len.toNat 0) (lastOK_of src dest sh strs hst hn)
  have hcopy : copyBuffer (st.mem ++ List.replicate src.len.toNat 0) (st.mem ++ List.replicate src.len.toNat 0)
      dest src = .ok (wrBytes (st.mem ++ List.replicate src.len.toNat 0) st.mem.length
        (flatBytes (st.mem ++ List.replicate src.len.toNat 0) src.itemsize sh strs src.suboffsets src.buf)) := by
    simp only [copyBuffer, bind, Except.bind, hequiv, pure, Except.pure]
    rw [show dest.shape.getD [] = sh by rw [hd]; rfl,
      show dest.strides.getD [] = cStrides src.itemsize sh by rw [hd]; rfl,
      show dest.suboffsets = none by rw [hd],
      show dest.buf = st.mem.length by rw [hd],
      show dest.itemsize = src.itemsize by rw [hd], hst]
    simp only [Option.getD_some]
    rw [hc]
  simp only [hmvs, hsh, Option.getD_some, true_or, ↓reduceIte, M.get, M.modify, M.lift, ← hdest,
    St.mem_setMv, hmem3, hcopy, M.pure_app]
  have hbound : ((st.mem.length : Int) + (flatBytes (st.mem ++ List.replicate src.len.toNat 0) src.itemsize sh
      strs src.suboffsets src.buf).length) ≤ (st.mem ++ List.replicate src.len.toNat 0).length := by
    simp only [List.length_append, List.length_replicate]
    omega
  have hrd := rdBytes_wrBytes (st.mem ++ List.replicate src.len.toNat 0) st.mem.length _ (by omega) hbound
  have hmv : ({ s3.setMv st.mvs.length { s3.mv st.mvs.length with view := dest, flags := initFlags dest } with
      mem := wrBytes (st.mem ++ List.replicate src.len.toNat 0) st.mem.length
        (flatBytes (st.mem ++ List.replicate src.len.toNat 0) src.itemsize sh strs src.suboffsets src.buf) } : St).mv
        st.mvs.length = { s3.mv st.mvs.length with view := dest, flags := initFlags dest } :=
    St.mv_setMv s3 _ _ hn3
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmv, hd]
  · rw [hmv, hd]
  · rw [hmv, hd, hf]
  · rw [hmv, hd]
  · rw [hmv, hd]
  · have e : src.len.toNat = (flatBytes (st.mem ++ List.replicate src.len.toNat 0) src.itemsize sh strs
        src.suboffsets src.buf).length := by omega
    exact (congrArg (rdBytes _ _) e).trans hrd

/-- `PyMemoryView_FromBuffer` on a `Py_buffer` that has only `buf`, `len` and `itemsize`, the case
its comment singles out ("init_shape_strides() must be able to reconstruct missing values",
:764-768): a 1-D view of `len / itemsize` items with stride `itemsize`, format `B`, and no
exporter (`mbuf_add_view`, `init_shape_strides`, `init_shared_values`). Hypothesis: `ndim == 1`,
the only way to pass a NULL shape. -/
def FromBufferReconstructs : Prop :=
  ∀ (st : St) (info : Buf), info.ndim = 1 → info.shape = none → info.strides = none →
    info.format = none → info.suboffsets = none →
    let r := memoryViewFromBuffer info false st
    let i := st.mvs.length
    let v := (r.2.mv i).view
    r.1 = .ok i ∧ v.obj = none ∧ v.buf = info.buf ∧ v.len = info.len ∧
      v.shape = some [Int.tdiv info.len info.itemsize] ∧ v.strides = some [info.itemsize] ∧
      v.format = some ['B']

theorem fromBufferReconstructs_proven : FromBufferReconstructs := by
  intro st info h1 hsh hst hfm hsb
  obtain ⟨b, hb⟩ : ∃ b : Buf, b = { info with obj := none } := ⟨_, rfl⟩
  obtain ⟨st2, hst2⟩ : ∃ s2, s2 = let st1 : St := { st with mbufs := st.mbufs ++ [{}] }
      st1.setMb st.mbufs.length { st1.mb st.mbufs.length with master := b } := ⟨_, rfl⟩
  have hmb : st2.mb st.mbufs.length = { master := b } := by
    rw [hst2]
    exact fresh_mb st b
  have e : memoryViewFromBuffer info false st = mbufAddView st.mbufs.length (some b) st2 := by
    have : memoryViewFromBuffer info false st = mbufAddView st.mbufs.length none st2 := by
      rw [hst2, hb]
      rfl
    rw [this, mbufAddView_none, hmb]
  have ⟨h2, hA⟩ := mbufAddView_added st.mbufs.length b st2 (by rw [hb]; show info.ndim ≤ 64; omega)
  have hmv : st2.mvs.length = st.mvs.length := by rw [hst2]; rfl
  rw [hmv] at h2
  have hnew : ((mbufAddView st.mbufs.length (some b) st2).2.mv st.mvs.length).view = viewCopy b := by
    have := hA.new
    rw [hmv] at this
    rw [this]
  dsimp only
  rw [e, hnew]
  have hvc : viewCopy b =
      { obj := none, buf := info.buf, len := info.len, itemsize := info.itemsize,
        readonly := info.readonly, ndim := 1, format := some ['B'],
        shape := some [Int.tdiv info.len info.itemsize], strides := some [info.itemsize],
        suboffsets := none, hook := info.hook } := by
    rw [hb]
    simp [viewCopy, initShapeStrides, initSharedValues, initSuboffsets, h1, hsh, hst, hfm, hsb]
  rw [hvc]
  exact ⟨h2, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The `order` argument of `tobytes` (:2286-2300): `None` and `'C'` are the same, and anything
but `'C'`, `'F'`, `'A'` raises `ValueError`. Hypothesis: a live view. -/
def TobytesOrderArg : Prop :=
  ∀ (st : St) (self : Nat) (o : List Char), baseInaccessible st self = false →
    memoryviewTobytes self (some ['C']) st = memoryviewTobytes self none st ∧
    (o ≠ ['C'] → o ≠ ['F'] → o ≠ ['A'] →
      memoryviewTobytes self (some o) st = (.error (.valueError "order must be 'C', 'F' or 'A'"), st))

theorem tobytesOrderArg_proven : TobytesOrderArg := by
  intro st self o hl
  have hc := checkReleased_ok st self hl
  refine ⟨by simp only [memoryviewTobytes, M.bind_app, hc, M.lift, parseOrder], fun h1 h2 h3 => ?_⟩
  have hp : parseOrder (some o) = .error (.valueError "order must be 'C', 'F' or 'A'") := by
    unfold parseOrder
    split
    all_goals first
      | rfl
      | (simp_all; done)
  simp only [memoryviewTobytes, M.bind_app, hc, M.lift, hp]

/-! ## Stated, not settled -/

/-- See the registry entry `bytesobj-memoryview-float32-round-trip`. -/
def Float32RoundTrip : Prop :=
  ∀ x : Nat, x < 2 ^ 32 → ¬ (x / 2 ^ 23 % 256 = 255 ∧ x % 2 ^ 23 ≠ 0) → narrow32 (widen32 x) = x

/-- See the registry entry `bytesobj-memoryview-float16-round-trip`. -/
def Float16RoundTrip : Prop :=
  ∀ x : Nat, x < 2 ^ 16 → ¬ (x / 2 ^ 10 % 32 = 31 ∧ x % 2 ^ 10 ≠ 0) → pack2 (unpack2 x) = .ok x

/-- See the registry entry `bytesobj-memoryview-tobytes-contig-nd`. -/
def TobytesContigND : Prop :=
  ∀ (m : Mem) (v : Buf) (sh st : List Int), v.shape = some sh → v.strides = some st → sh ≠ [] →
    sh.length = v.ndim → (∀ x ∈ sh, 0 ≤ x) → 0 < v.itemsize → v.len = prod sh * v.itemsize →
    v.suboffsets = none → pyBufferIsContiguous v 'C' = true →
    rdBytes m v.buf v.len.toNat = flatBytes m v.itemsize sh st none v.buf

/-- See the registry entry `bytesobj-memoryview-tobytes-fortran`. -/
def TobytesFortran2D : Prop :=
  ∀ (m : Mem) (v : Buf) (a b : Nat) (s t : Int), v.shape = some [(a : Int), (b : Int)] →
    v.strides = some [s, t] → v.ndim = 2 → 0 < v.itemsize → v.len = (a : Int) * b * v.itemsize →
    v.suboffsets = none →
    bufferToContiguous m v 'F' = .ok ((List.range b).flatMap fun (j : Nat) =>
      (List.range a).flatMap fun (i : Nat) =>
        rdBytes m (v.buf + s * (i : Int) + t * (j : Int)) v.itemsize.toNat)

end PyLean.BytesObj.Mem
