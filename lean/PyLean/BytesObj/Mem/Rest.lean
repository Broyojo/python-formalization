import PyLean.BytesObj.Mem.Iter

/-!
`hash`, `memory_getbuf`, and the constructors from exporters and raw memory.
-/

namespace PyLean.BytesObj.Mem

open PyLean

/-! ## Hash -/

/-- The conditions under which `hash(m)` reaches `Py_HashBuffer`. -/
structure Hashable (st : St) (i : Nat) : Prop where
  valid : i < st.mvs.length
  live : baseInaccessible st i = false
  fresh : (st.mv i).hash = none
  readonly : (st.mv i).view.readonly = true
  format : ∃ c size, getNativeFmtchar ((st.mv i).view.format.getD []) = some (c, size) ∧ isByteFormat c = true
  obj : (st.mv i).view.obj = none ∨ ∃ e, (st.mv i).view.obj = some (.exp e) ∧ st.unhashable.getD e none = none

theorem memoryHash_contig (st : St) (i : Nat) (h : Hashable st i) (hC : (st.mv i).flags.isC = true) :
    memoryHash i st =
      (.ok (rdBytes st.mem (st.mv i).view.buf (st.mv i).view.len.toNat),
       st.setMv i { st.mv i with hash := some (rdBytes st.mem (st.mv i).view.buf (st.mv i).view.len.toNat) }) := by
  obtain ⟨c, size, hf, hb⟩ := h.format
  have hc := checkReleased_ok st i h.live
  unfold memoryHash
  simp only [memoryHashF, M.bind_app, M.get, h.fresh, hc, h.readonly, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, hf, hb, M.pure_app, hC, M.modify]
  rcases h.obj with ho | ⟨e, ho, hu⟩
  · simp only [ho]
    rfl
  · simp only [ho, hu]
    rfl

theorem memoryHash_strided (st : St) (i : Nat) (b : List Nat) (h : Hashable st i)
    (hC : (st.mv i).flags.isC = false)
    (hb2 : bufferToContiguous st.mem (st.mv i).view 'C' = .ok b) :
    memoryHash i st = (.ok b, st.setMv i { st.mv i with hash := some b }) := by
  obtain ⟨c, size, hf, hb⟩ := h.format
  have hc := checkReleased_ok st i h.live
  unfold memoryHash
  simp only [memoryHashF, M.bind_app, M.get, h.fresh, hc, h.readonly, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, hf, hb, M.pure_app, hC, M.modify, Bool.not_false, M.lift, hb2]
  rcases h.obj with ho | ⟨e, ho, hu⟩
  · simp only [ho]
    rfl
  · simp only [ho, hu]
    rfl

/-- `hash(m) == hash(m.tobytes())` for every read-only 1-D view of a byte format, for every
stride (Doc/library/stdtypes.rst, `memoryview.__hash__`), and the value stays: a later `hash`
gives the same even after `release()`. Hypotheses: the conditions of the function itself
(read-only, byte format, hashable exporter), and the type invariants of the view. -/
def HashIsTobytes : Prop :=
  ∀ (st : St) (self : Nat) (n d : Int) (f : List Char),
    Live1D st self n d f → Hashable st self → 0 < (st.mv self).view.itemsize →
    (st.mv self).view.len = n * (st.mv self).view.itemsize →
    (st.mv self).flags.isC = (initFlags (st.mv self).view).isC →
    (memoryHash self st).1 = (memoryviewTobytes self none st).1 ∧
    (∀ s', (s'.mv self).hash = ((memoryHash self st).2.mv self).hash →
      (memoryHash self s').1 = (memoryHash self st).1)

theorem hash_cached (s : St) (self : Nat) (b : List Nat) (h : (s.mv self).hash = some b) :
    (memoryHash self s).1 = .ok b := by
  unfold memoryHash
  simp only [memoryHashF, M.bind_app, M.get, h, M.pure_app]

theorem hashIsTobytes_proven : HashIsTobytes := by
  intro st self n d f hL hH hit hlen hfl
  have ht := tobytes1D_proven st self n d f hL hit hlen
  rw [ht]
  by_cases hC : (st.mv self).flags.isC = true
  · rw [memoryHash_contig st self hH hC]
    have hc := isC_contig _ (hfl ▸ hC) hL.subs
    have hp : pyBufferToContiguous st.mem (st.mv self).view (st.mv self).view.len 'C' =
        .ok (rdBytes st.mem (st.mv self).view.buf (st.mv self).view.len.toNat) := by
      simp [pyBufferToContiguous, hc]
    have ht2 : memoryviewTobytes self none st =
        (.ok (rdBytes st.mem (st.mv self).view.buf (st.mv self).view.len.toNat), st) := by
      simp only [memoryviewTobytes, M.bind_app, checkReleased_ok _ _ hL.live, M.pure_app, M.get, M.lift, hp,
        parseOrder]
    have heq := ht2.symm.trans ht
    simp only [Prod.mk.injEq, Except.ok.injEq, and_true] at heq
    refine ⟨by rw [heq], fun s' hs => ?_⟩
    rw [St.mv_setMv _ _ _ hL.valid] at hs
    exact hash_cached s' self _ hs
  · have hCf : (st.mv self).flags.isC = false := by simpa using hC
    have hb := tobytesC_proven st.mem (st.mv self).view [n] [d] hL.shape hL.strides (by simp)
      (by simp [hL.ndim]) (by simpa using hL.nonneg) hit (by simp [prod, hlen])
    rw [hL.subs] at hb
    rw [memoryHash_strided st self _ hH hCf hb]
    refine ⟨rfl, fun s' hs => ?_⟩
    rw [St.mv_setMv _ _ _ hL.valid] at hs
    exact hash_cached s' self _ hs

/-- Refusals of `hash`: a writable view, then a non-byte format (:3217-3227). -/
def HashRejections : Prop :=
  ∀ (st : St) (self : Nat), baseInaccessible st self = false → (st.mv self).hash = none →
    ((st.mv self).view.readonly = false →
      (memoryHash self st).1 = .error (.valueError "cannot hash writable memoryview object")) ∧
    ((st.mv self).view.readonly = true →
      ∀ c size, getNativeFmtchar ((st.mv self).view.format.getD []) = some (c, size) →
        isByteFormat c = false →
        (memoryHash self st).1 =
          .error (.valueError "memoryview: hashing is restricted to formats 'B', 'b' or 'c'"))

theorem hashRejections_proven : HashRejections := by
  intro st self hl hf
  have hc := checkReleased_ok st self hl
  constructor
  · intro h
    unfold memoryHash
    simp only [memoryHashF, M.bind_app, M.get, hf, hc, h, Bool.not_false, ↓reduceIte, M.throw_app]
  · intro h c size hfm hb
    unfold memoryHash
    simp only [memoryHashF, M.bind_app, M.get, hf, hc, h, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      hfm, hb, M.pure_app, M.throw_app, Bool.not_false]

/-! ## `memory_getbuf` -/

/-- `memory_getbuf`: a failed request changes nothing; a successful one adds one export and
hands out the view with `obj` set to the memoryview and the same memory; without
`PyBUF_FORMAT` the format is NULL and without `PyBUF_ND` the buffer is 1-D with no shape
(:1529-1606). A request for writing a read-only view is refused first. `memory_releasebuf`
takes the export back. Hypotheses: a live, unrestricted view. -/
def GetbufRules : Prop :=
  ∀ (st : St) (self flags : Nat), self < st.mvs.length →
    baseInaccessible st self = false → (st.mv self).flags.restricted = false →
    let r := memoryGetbuf self flags st
    let v := (st.mv self).view
    (∀ e, r.1 = .error e → r.2 = st) ∧
    (∀ b, r.1 = .ok b → b.obj = some (.mv self) ∧ b.buf = v.buf ∧ b.len = v.len ∧
      b.itemsize = v.itemsize ∧ b.readonly = v.readonly ∧
      (r.2.mv self).exports = (st.mv self).exports + 1 ∧
      ((flags &&& bufFormat) = 0 → b.format = none) ∧
      (req flags bufND = false → b.ndim = 1 ∧ b.shape = none) ∧
      (memoryReleasebuf self r.2).2.mv self = st.mv self) ∧
    ((flags &&& bufWritable) ≠ 0 → v.readonly = true →
      r.1 = .error (bufferError "memoryview: underlying buffer is not writable"))

theorem getbufView_ok (base : Buf) (f : Flags) (flags : Nat) (b : Buf)
    (h : getbufView base f flags = .ok b) :
    b.buf = base.buf ∧ b.len = base.len ∧ b.itemsize = base.itemsize ∧ b.readonly = base.readonly ∧
    ((flags &&& bufFormat) = 0 → b.format = none) ∧ (req flags bufND = false → b.ndim = 1 ∧ b.shape = none) := by
  unfold getbufView at h
  dsimp only at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  simp only [Except.ok.injEq] at h
  subst h
  have hfield : ∀ v : Buf, (viewFormat flags v).buf = v.buf ∧ (viewFormat flags v).len = v.len ∧
      (viewFormat flags v).itemsize = v.itemsize ∧ (viewFormat flags v).readonly = v.readonly := by
    intro v; unfold viewFormat; split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  have hfield2 : ∀ v : Buf, (viewStrides flags v).buf = v.buf ∧ (viewStrides flags v).len = v.len ∧
      (viewStrides flags v).itemsize = v.itemsize ∧ (viewStrides flags v).readonly = v.readonly ∧
      (viewStrides flags v).format = v.format := by
    intro v; unfold viewStrides; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hfield3 : ∀ v : Buf, (viewShape flags v).buf = v.buf ∧ (viewShape flags v).len = v.len ∧
      (viewShape flags v).itemsize = v.itemsize ∧ (viewShape flags v).readonly = v.readonly ∧
      (viewShape flags v).format = v.format := by
    intro v; unfold viewShape; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  generalize hv1 : viewFormat flags { base with obj := none } = v1
  have hv1f := hfield { base with obj := none }
  rw [hv1] at hv1f
  have hfmt : (flags &&& bufFormat) = 0 → v1.format = none := by
    intro h0
    rw [← hv1]
    simp [viewFormat, h0]
  have h2 := hfield2 v1
  generalize viewStrides flags v1 = v2 at *
  have h3 := hfield3 v2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h3.1, h2.1, hv1f.1]
  · rw [h3.2.1, h2.2.1, hv1f.2.1]
  · rw [h3.2.2.1, h2.2.2.1, hv1f.2.2.1]
  · rw [h3.2.2.2.1, h2.2.2.2.1, hv1f.2.2.2]
  · intro h0
    rw [h3.2.2.2.2, h2.2.2.2.2, hfmt h0]
  · intro h0
    simp [viewShape, h0]

theorem getbufRules_proven : GetbufRules := by
  intro st self flags hs hl hr
  have hc := checkReleased_ok st self hl
  have hc2 := checkRestricted_ok st self hr
  dsimp only
  have hgb : memoryGetbuf self flags st =
      match getbufView (st.mv self).view (st.mv self).flags flags with
      | .error e => (.error e, st)
      | .ok v => (.ok { v with obj := some (.mv self) },
          st.setMv self { st.mv self with exports := (st.mv self).exports + 1 }) := by
    simp only [memoryGetbuf, M.bind_app, hc, hc2, M.get, M.lift]
    cases getbufView (st.mv self).view (st.mv self).flags flags <;> rfl
  rw [hgb]
  refine ⟨?_, ?_, ?_⟩
  · intro e h
    cases hv : getbufView (st.mv self).view (st.mv self).flags flags with
    | error x => rfl
    | ok v => rw [hv] at h; cases h
  · intro b h
    cases hv : getbufView (st.mv self).view (st.mv self).flags flags with
    | error x => rw [hv] at h; cases h
    | ok v =>
      rw [hv] at h
      simp only [Except.ok.injEq] at h
      subst h
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := getbufView_ok _ _ _ _ hv
      refine ⟨rfl, h1, h2, h3, h4, ?_, h5, h6, ?_⟩
      · rw [St.mv_setMv _ _ _ hs]
      · have hrel : memoryReleasebuf self
            (st.setMv self { st.mv self with exports := (st.mv self).exports + 1 }) =
            (.ok (), (st.setMv self { st.mv self with exports := (st.mv self).exports + 1 }).setMv self
              { (st.setMv self { st.mv self with exports := (st.mv self).exports + 1 }).mv self with
                exports := ((st.setMv self { st.mv self with exports := (st.mv self).exports + 1 }).mv self).exports - 1 }) := rfl
        rw [hrel]
        simp only []
        rw [St.mv_setMv _ _ _ (by simpa [St.setMv] using hs), St.mv_setMv _ _ _ hs]
        simp
  · intro h1 h2
    have : ((flags &&& bufWritable) != 0 && (st.mv self).view.readonly) = true := by
      simp [h1, h2]
    simp [getbufView, this]

/-! ## Constructors -/

/-- `memoryview(x)` of a 1-D exporter: a new managed buffer with one registered view, whose
master is what the exporter gave, and whose view is the exporter's buffer
(`mbuf_alloc`, `_PyManagedBuffer_FromObject`, `PyMemoryView_FromObjectAndFlags`,
`PyMemoryView_FromObject`, `memoryview_impl`, :71-104, :800-857, :1013-1018). Hypotheses: the
exporter's buffer has full information. -/
def NewFromExporter : Prop :=
  ∀ (st : St) (b : Buf) (n d : Int) (f : List Char),
    b.ndim = 1 → b.shape = some [n] → b.strides = some [d] → b.suboffsets = none → b.format = some f →
    let r := memoryviewNew (.exporter (.val b) none) st
    let i := st.mvs.length
    let k := st.mbufs.length
    r.1 = .ok i ∧ (r.2.mv i).view = b ∧ (r.2.mv i).mbuf = k ∧ (r.2.mb k).exports = 1 ∧
      (r.2.mb k).released = false ∧ (r.2.mb k).master = b ∧ r.2.mem = st.mem

theorem simpleGetbuffer_full (b : Buf) (f : List Char) (hf : b.format = some f) (hs : b.suboffsets = none) :
    simpleGetbuffer b bufFullRO = .ok b ∨ b.readonly = true := by
  have h1 : req bufFullRO bufWritable = false := by decide
  have h2 : req bufFullRO bufFormat = true := by decide
  have h3 : req bufFullRO bufND = true := by decide
  have h4 : req bufFullRO bufStrides = true := by decide
  have h5 : req bufFullRO bufIndirect = true := by decide
  left
  simp [simpleGetbuffer, h1, h2, h3, h4, h5]
  try (cases b; simp_all)

theorem mbufAddView_none (k : Nat) (st : St) :
    mbufAddView k none st = mbufAddView k (some (st.mb k).master) st := rfl

theorem fresh_mb (st : St) (b : Buf) :
    let k := st.mbufs.length
    let st1 : St := { st with mbufs := st.mbufs ++ [{}] }
    (st1.setMb k { st1.mb k with master := b }).mb k = { master := b } := by
  intro k st1
  have hk : k < st1.mbufs.length := by simp [st1, k]
  rw [St.mb_setMb _ _ _ hk]
  have : st1.mb k = {} := by
    simp [St.mb, st1, k, List.getD_eq_getElem?_getD]
  rw [this]

theorem newFromExporter_proven : NewFromExporter := by
  intro st b n d f h1 hsh hst hsb hf
  have hg : simpleGetbuffer b bufFullRO = .ok b := by
    rcases simpleGetbuffer_full b f hf hsb with h | h
    · exact h
    · have h1' : req bufFullRO bufWritable = false := by decide
      have h2 : req bufFullRO bufFormat = true := by decide
      have h3 : req bufFullRO bufND = true := by decide
      have h4 : req bufFullRO bufStrides = true := by decide
      have h5 : req bufFullRO bufIndirect = true := by decide
      simp [simpleGetbuffer, h1', h2, h3, h4, h5, hsb]
      try (cases b; simp_all)
  have hview := viewCopy_1d b n d f h1 hsh hst hsb hf
  dsimp only
  obtain ⟨st2, hst2⟩ : ∃ s2, s2 = let st1 : St := { st with mbufs := st.mbufs ++ [{}] }
      st1.setMb st.mbufs.length { st1.mb st.mbufs.length with master := b } := ⟨_, rfl⟩
  have hmb : st2.mb st.mbufs.length = { master := b } := by
    rw [hst2]
    exact fresh_mb st b
  have hlen : st2.mbufs.length = st.mbufs.length + 1 := by
    rw [hst2]
    simp [St.setMb]
  have e : memoryviewNew (.exporter (.val b) none) st = mbufAddView st.mbufs.length (some b) st2 := by
    simp only [memoryviewNew, memoryViewFromObject, memoryViewFromObjectAndFlags, M.bind_app, fire,
      M.pure_app, viewOfExporter, managedBufferFromObject, mbufAlloc, M.lift, hg, M.modify, Ret.get_val]
    rw [← hst2]
    rw [show (M.onError (mbufAddView st.mbufs.length none) (mbufRelease st.mbufs.length)) st2 =
      mbufAddView st.mbufs.length (some b) st2 from ?_]
    have hn : mbufAddView st.mbufs.length none st2 = mbufAddView st.mbufs.length (some b) st2 := by
      rw [mbufAddView_none, hmb]
    have ⟨h2, _⟩ := mbufAddView_added st.mbufs.length b st2 (by omega)
    simp only [M.onError, hn]
    rcases hrr : mbufAddView st.mbufs.length (some b) st2 with ⟨r, s⟩
    rw [hrr] at h2
    simp only at h2
    subst h2
    rfl
  have ⟨h2, hA⟩ := mbufAddView_added st.mbufs.length b st2 (by omega)
  rw [hview] at hA
  rw [e]
  have hmv : st2.mvs.length = st.mvs.length := by rw [hst2]; rfl
  have hmem : st2.mem = st.mem := by rw [hst2]; rfl
  rw [hmv] at h2
  have hnew : ((mbufAddView st.mbufs.length (some b) st2).2.mv st.mvs.length) =
      { mbuf := st.mbufs.length, view := b, flags := initFlags b } := by
    have := hA.new
    rwa [hmv] at this
  have hk : st.mbufs.length < st2.mbufs.length := by omega
  refine ⟨h2, by rw [hnew], by rw [hnew], ?_, ?_, ?_, ?_⟩
  · rw [hA.exports hk, hmb]; rfl
  · rw [hA.released hk, hmb]
  · rw [hA.master hk, hmb]
  · rw [hA.mem, hmem]

/-- `PyMemoryView_FromMemory`: a byte view with no exporter, read-only or writable as asked,
contiguous; `PyMemoryView_FromBuffer` refuses a NULL `buf` (:740-794). -/
def FromMemorySpec : Prop :=
  ∀ (st : St) (mem size : Int) (w : Bool) (info : Buf),
    (let r := memoryViewFromMemory mem size w st
     let i := st.mvs.length
     let v := (r.2.mv i).view
     r.1 = .ok i ∧ v.buf = mem ∧ v.len = size ∧ v.readonly = !w ∧ v.obj = none ∧
       v.format = some ['B'] ∧ v.shape = some [size] ∧ (r.2.mv i).flags.isC = true) ∧
    memoryViewFromBuffer info true st =
      (.error (.valueError "PyMemoryView_FromBuffer(): info->buf must not be NULL"), st)

theorem fromMemorySpec_proven : FromMemorySpec := by
  intro st mem size w info
  refine ⟨?_, by simp [memoryViewFromBuffer, M.bind_app, M.throw_app]⟩
  obtain ⟨b, hb⟩ : ∃ b : Buf, b =
      { buf := mem, len := size, itemsize := 1, readonly := !w, ndim := 1,
        format := some ['B'], shape := some [size], strides := some [1] } := ⟨_, rfl⟩
  have hview : viewCopy b = b := viewCopy_1d b size 1 ['B'] (by rw [hb]) (by rw [hb]) (by rw [hb])
    (by rw [hb]) (by rw [hb])
  obtain ⟨st2, hst2⟩ : ∃ s2, s2 = let st1 : St := { st with mbufs := st.mbufs ++ [{}] }
      st1.setMb st.mbufs.length { st1.mb st.mbufs.length with master := b } := ⟨_, rfl⟩
  have hmb : st2.mb st.mbufs.length = { master := b } := by
    rw [hst2]
    exact fresh_mb st b
  have e : memoryViewFromMemory mem size w st = mbufAddView st.mbufs.length (some b) st2 := by
    have : memoryViewFromMemory mem size w st = mbufAddView st.mbufs.length none st2 := by
      rw [hst2, hb]
      rfl
    rw [this, mbufAddView_none, hmb]
  have ⟨h2, hA⟩ := mbufAddView_added st.mbufs.length b st2 (by rw [hb]; show 1 ≤ 64; omega)
  rw [hview] at hA
  have hmv : st2.mvs.length = st.mvs.length := by rw [hst2]; rfl
  rw [hmv] at h2
  have hnew : ((mbufAddView st.mbufs.length (some b) st2).2.mv st.mvs.length) =
      { mbuf := st.mbufs.length, view := b, flags := initFlags b } := by
    have := hA.new
    rwa [hmv] at this
  dsimp only
  rw [e, hnew]
  refine ⟨h2, by rw [hb], by rw [hb], by rw [hb], by rw [hb], by rw [hb], by rw [hb], ?_⟩
  rw [hb]
  simp [initFlags, mvContiguousNdim1, Flags.isC]

end PyLean.BytesObj.Mem
