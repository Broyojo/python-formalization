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
  · unfold pyBufferRelease
    split <;> rfl

theorem memoryRelease_ok (i : Nat) (st : St) : (memoryRelease i st).1 = .ok () := by
  unfold memoryRelease
  dsimp only
  split
  · rfl
  · split
    · exact mbufRelease_ok _ _
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
  have hdeal : ∀ s, (memoryDealloc st.mvs.length s).1 = .ok () := fun s => memoryRelease_ok _ _
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
  ∀ (st : St) (src : Buf) (sh strs : List Int), src.shape = some sh → src.strides = some strs →
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

end PyLean.BytesObj.Mem
