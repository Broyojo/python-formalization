import PyLean.BytesObj.Mem.Evil
import PyLean.Sequences.SliceAssign

/-!
Indexing and slicing: which address each item of a view lives at, for one-dimensional
views of any stride.
-/

namespace PyLean.BytesObj.Mem

open PyLean
open PyLean.RangeSlice (Slice sliceUnpack adjustIndices sliceIndices IsLen wrap toU two64
  indices_in_bounds)

theorem wrap_id (x : Int) (h : -9223372036854775808 ≤ x ∧ x ≤ 9223372036854775807) : wrap x = x := by
  unfold wrap RangeSlice.two64 RangeSlice.longMax
  split <;> omega

theorem wrap_mul (d x n : Int) (hx : -n ≤ x ∧ x ≤ n) (hD : (d.natAbs : Int) * n ≤ ssizeMax) :
    wrap (d * x) = d * x := by
  have h1 : (d * x).natAbs = d.natAbs * x.natAbs := Int.natAbs_mul d x
  have hn : 0 ≤ n := by omega
  have h2 : x.natAbs ≤ n.toNat := by omega
  have h3 : d.natAbs * x.natAbs ≤ d.natAbs * n.toNat := Nat.mul_le_mul_left _ h2
  have h4 : ((d.natAbs * n.toNat : Nat) : Int) = (d.natAbs : Int) * n := by
    rw [Int.natCast_mul, Int.toNat_of_nonneg hn]
  have h5 : ((d * x).natAbs : Int) ≤ ssizeMax := by
    have : ((d * x).natAbs : Int) ≤ ((d.natAbs * n.toNat : Nat) : Int) := by
      rw [h1]; exact_mod_cast h3
    omega
  unfold ssizeMax at h5
  apply wrap_id
  omega

theorem sliceUnpack_step (s : Slice) (a b c : Int) (h : sliceUnpack s = .ok (a, b, c)) :
    -ssizeMax ≤ c ∧ c ≤ ssizeMax := by
  unfold sliceUnpack at h
  simp only [bind, Except.bind] at h
  cases hs : s.step with
  | none =>
    simp only [hs, pure, Except.pure] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    unfold ssizeMax; omega
  | some v =>
    simp only [hs] at h
    split at h
    · simp at h
    · rename_i hz
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, -, hc⟩ := h
      have : RangeSlice.clampSsize v ≤ ssizeMax := by
        unfold RangeSlice.clampSsize ssizeMin ssizeMax; split <;> (try split) <;> omega
      rw [← hc]
      split <;> (unfold ssizeMax at *; omega)

/-- What `init_slice` does to a 1-D view. -/
theorem initSlice_spec (v : Buf) (s : Slice) (n d : Int) (hsh : v.shape = some [n])
    (hst : v.strides = some [d]) (hn : 0 ≤ n) (hn' : n ≤ ssizeMax)
    (hD : (d.natAbs : Int) * n ≤ ssizeMax) (h0 : s.step ≠ some 0) :
    ∃ a b c L w, sliceIndices s n = .ok (a, b, c) ∧ IsLen a b c L ∧ 0 ≤ L ∧
      initSlice v s 0 = .ok w ∧ w.shape = some [L] ∧ w.ndim = v.ndim ∧ w.itemsize = v.itemsize ∧
      w.format = v.format ∧ w.suboffsets = v.suboffsets ∧ w.readonly = v.readonly ∧
      ∀ k, 0 ≤ k → k < L → (0 ≤ a + k * c ∧ a + k * c < n) ∧
        w.buf + k * (w.strides.getD []).getD 0 0 = v.buf + d * (a + k * c) := by
  obtain ⟨a, b, c, L, st, sp, c', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    Sequences.adjust_spec s n hn hn' h0
  have hb := indices_in_bounds a b c n L h2 h3
  have hstep := sliceUnpack_step s _ _ _ h5
  have hinit : initSlice v s 0 = .ok { v with
      buf := v.buf + wrap (d * a), shape := some [L], strides := some [wrap (d * c')] } := by
    simp only [initSlice, bind, Except.bind, h5, pure, Except.pure, hsh, hst, Option.getD_some,
      List.getD_cons_zero, h6]
    cases hsb : v.suboffsets <;> rfl
  refine ⟨a, b, c, L, _, h1, h2, h2.1, hinit, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro k hk hkL
  have hbk := hb k hk hkL
  refine ⟨hbk, ?_⟩
  have h0a := hb 0 (by omega) (by omega)
  have ha : wrap (d * a) = d * a := wrap_mul d a n (by simp at h0a; omega) hD
  by_cases hk0 : k = 0
  · subst hk0
    simp [ha]
  · have h1b := hb 1 (by omega) (by omega)
    have hu := h11 1 (by omega) (by omega)
    simp only [Int.one_mul] at h1b hu
    have hcc : c' = c := by
      unfold toU two64 at hu
      unfold ssizeMax at hstep hn'
      omega
    subst hcc
    have hw : wrap (d * c') = d * c' := wrap_mul d c' n (by simp at h0a; omega) hD
    simp only [Option.getD_some, List.getD_cons_zero, ha, hw, Int.mul_add]
    rw [Int.add_assoc, Int.mul_left_comm k d c']

/-- A live view with full information whose copy `mbuf_add_view` makes is itself. -/
def viewCopy (src : Buf) : Buf :=
  let (sh, stridesOut) := initShapeStrides src
  { initSharedValues { ndim := src.ndim } src with
    shape := sh, strides := stridesOut, suboffsets := initSuboffsets src }

theorem mbufAddView_added (k : Nat) (src : Buf) (st : St) (h : src.ndim ≤ 64) :
    (mbufAddView k (some src) st).1 = .ok st.mvs.length ∧
    Added st (mbufAddView k (some src) st).2 k
      { mbuf := k, view := viewCopy src, flags := initFlags (viewCopy src) } := by
  have h' : ¬ src.ndim > 64 := by omega
  have e : mbufAddView k (some src) st =
      (.ok st.mvs.length,
       let st0 : St := { st with mvs := st.mvs ++
         [{ mbuf := k, view := viewCopy src, flags := initFlags (viewCopy src) }] }
       st0.setMb k { st0.mb k with exports := (st0.mb k).exports + 1 }) := by
    simp only [mbufAddView, M.bind_app, M.get, Option.getD_some, h', ↓reduceIte]
    rfl
  rw [e]
  exact ⟨rfl, added_of st k _⟩

theorem viewCopy_1d (v : Buf) (n d : Int) (f : List Char) (h1 : v.ndim = 1) (hsh : v.shape = some [n])
    (hst : v.strides = some [d]) (hsub : v.suboffsets = none ∨ ∃ o, v.suboffsets = some [o])
    (hf : v.format = some f) : viewCopy v = v := by
  cases v
  rcases hsub with hsub | ⟨o, hsub⟩ <;>
    simp_all [viewCopy, initShapeStrides, initSharedValues, initSuboffsets]

/-- A 1-D view of `n` items, stride `d`: `self` is a live, unrestricted object. -/
structure Live1D (st : St) (i : Nat) (n d : Int) (f : List Char) : Prop where
  valid : i < st.mvs.length
  mbuf : (st.mv i).mbuf < st.mbufs.length
  live : baseInaccessible st i = false
  unres : (st.mv i).flags.restricted = false
  ndim : (st.mv i).view.ndim = 1
  shape : (st.mv i).view.shape = some [n]
  strides : (st.mv i).view.strides = some [d]
  subs : (st.mv i).view.suboffsets = none ∨ ∃ o, (st.mv i).view.suboffsets = some [o]
  format : (st.mv i).view.format = some f
  nonneg : 0 ≤ n
  bound : n ≤ ssizeMax
  span : (d.natAbs : Int) * n ≤ ssizeMax

/-- `m[s]` of a 1-D view is a new view on the same memory whose `k`-th item is item
`range(*s.indices(n))[k]` of `m`, for every slice with a non-zero step: `len` is the length
of that range, every position is in `[0, n)`, and `nbytes` is `len * itemsize`. The bound
`|stride| * n <= sys.maxsize` is a type invariant of a buffer in the address space. -/
def SliceItems : Prop :=
  ∀ (st : St) (self : Nat) (s : Slice) (n d : Int) (f : List Char),
    Live1D st self n d f → s.step ≠ some 0 →
    ∃ a b c L, sliceIndices s n = .ok (a, b, c) ∧ IsLen a b c L ∧
      let r := memorySubscript self (.one (.slice s none)) st
      let w := (r.2.mv st.mvs.length).view
      r.1 = .ok (.view st.mvs.length) ∧ r.2.mem = st.mem ∧ w.shape = some [L] ∧ w.ndim = 1 ∧
      w.len = L * (st.mv self).view.itemsize ∧ w.format = some f ∧
      w.suboffsets = (st.mv self).view.suboffsets ∧
      ∀ k, 0 ≤ k → k < L → (0 ≤ a + k * c ∧ a + k * c < n) ∧
        w.buf + k * (w.strides.getD []).getD 0 0 = (st.mv self).view.buf + d * (a + k * c)

theorem sliceItems_proven : SliceItems := by
  intro st self s n d f hL h0
  have hview : viewCopy (st.mv self).view = (st.mv self).view :=
    viewCopy_1d _ n d f hL.ndim hL.shape hL.strides hL.subs hL.format
  obtain ⟨a, b, c, L, w, h1, h2, h3, hi, hws, hwn, hwi, hwf, hwsub, hwro, hk⟩ :=
    initSlice_spec (st.mv self).view s n d hL.shape hL.strides hL.nonneg hL.bound hL.span h0
  refine ⟨a, b, c, L, h1, h2, ?_⟩
  have hnd : ¬ (st.mv self).view.ndim = 0 := by rw [hL.ndim]; omega
  have ⟨hr1, hA⟩ := mbufAddView_added (st.mv self).mbuf (st.mv self).view st (by rw [hL.ndim]; omega)
  rw [hview] at hA
  have hmemsub : memorySubscript self (.one (.slice s none)) st =
      ((.ok (.view st.mvs.length)), St.setMv (mbufAddView (st.mv self).mbuf (some (st.mv self).view) st).2
        st.mvs.length
        { mbuf := (st.mv self).mbuf, view := { w with len := initLen (w.shape.getD []) w.itemsize },
          flags := initFlags { w with len := initLen (w.shape.getD []) w.itemsize } }) := by
    simp only [memorySubscript, M.bind_app, checkReleased_ok _ _ hL.live, M.get, hnd, ↓reduceIte,
      checkRestricted_ok _ _ hL.unres]
    rcases hrr : mbufAddView (st.mv self).mbuf (some (st.mv self).view) st with ⟨r1, st1⟩
    rw [hrr] at hr1 hA
    simp only at hr1 hA
    subst hr1
    simp only [M.onError, M.bind_app, sliceEvents_none s h0, M.pure_app, M.get, M.lift, hA.new, hi, M.modify]
  rw [hmemsub]
  have hn1 : st.mvs.length < (mbufAddView (st.mv self).mbuf (some (st.mv self).view) st).2.mvs.length := by
    rw [hA.len]; omega
  dsimp only
  rw [St.mv_setMv _ _ _ hn1]
  dsimp only
  refine ⟨rfl, hA.mem, hws, by rw [hwn, hL.ndim], ?_, by rw [hwf, hL.format], hwsub, hk⟩
  rw [hws, hwi]
  simp [initLen]

/-- The position `lookup_dimension` computes for an in-range index. -/
def pos (i n : Int) : Int := if i < 0 then i + n else i

/-- `m[i]` of a 1-D view with a single-character format, for every int `i`: outside
`Py_ssize_t` an `IndexError`, between `-n` and `n` the item at `buf + stride * position`
(reached through the suboffset if there is one), otherwise `IndexError("index out of bounds
on dimension 1")`. Nothing changes. Doc/library/stdtypes.rst, `memoryview`. -/
def IndexItem : Prop :=
  ∀ (st : St) (self : Nat) (i n d : Int) (f fmt : List Char),
    Live1D st self n d f → adjustFmt (st.mv self).view = .ok fmt →
    let r := memorySubscript self (.one (.obj (.int i))) st
    r.2 = st ∧
    (¬ (ssizeMin ≤ i ∧ i ≤ ssizeMax) →
      r.1 = .error (.indexError "cannot fit 'int' into an index-sized integer")) ∧
    (ssizeMin ≤ i → i ≤ ssizeMax → -n ≤ i → i < n →
      r.1 = Sub.item <$> unpackRaw st.mem
        (adjustPtr st.mem ((st.mv self).view.buf + d * pos i n) (st.mv self).view.suboffsets 0) fmt) ∧
    (ssizeMin ≤ i → i ≤ ssizeMax → ¬ (-n ≤ i ∧ i < n) →
      r.1 = .error (.indexError "index out of bounds on dimension 1"))

theorem lookup_in (m : Mem) (v : Buf) (ptr i n d : Int) (hsh : v.shape = some [n])
    (hst : v.strides = some [d]) (h : -n ≤ i ∧ i < n) :
    lookupDimension m v ptr 0 i = .ok (adjustPtr m (ptr + d * pos i n) v.suboffsets 0) := by
  simp only [lookupDimension, hsh, hst, Option.getD_some, List.getD_cons_zero]
  unfold pos
  split <;> (rename_i hc)
  · rw [if_neg (by omega)]
  · rw [if_neg (by omega)]

theorem lookup_out (m : Mem) (v : Buf) (ptr i n : Int) (hsh : v.shape = some [n])
    (h : ¬ (-n ≤ i ∧ i < n)) :
    lookupDimension m v ptr 0 i = .error (.indexError "index out of bounds on dimension 1") := by
  simp only [lookupDimension, hsh, Option.getD_some, List.getD_cons_zero]
  rw [if_pos]
  rfl
  split <;> omega

theorem unpackSingle_live (st : St) (self : Nat) (ptr : Int) (fmt : List Char)
    (h : baseInaccessible st self = false) :
    unpackSingle self ptr fmt st = (unpackRaw st.mem ptr fmt, st) := by
  simp only [unpackSingle, M.bind_app, checkReleased_ok _ _ h, M.get, M.lift]

/-- `memory_item` for a 1-D live view. -/
theorem memoryItem_eq (st : St) (self : Nat) (index n d : Int) (f fmt : List Char)
    (hL : Live1D st self n d f) (hf : adjustFmt (st.mv self).view = .ok fmt) :
    memoryItem self index st =
      match lookupDimension st.mem (st.mv self).view (st.mv self).view.buf 0 index with
      | .ok ptr => (unpackRaw st.mem ptr fmt, st)
      | .error e => (.error e, st) := by
  have hnd : ¬ (st.mv self).view.ndim = 0 := by rw [hL.ndim]; omega
  simp only [memoryItem, M.bind_app, checkReleased_ok _ _ hL.live, M.get, M.lift, hf, hL.ndim,
    Nat.one_ne_zero, ↓reduceIte, ptrFromIndex, M.pure_app]
  cases lookupDimension st.mem (st.mv self).view (st.mv self).view.buf 0 index with
  | error e => rfl
  | ok ptr =>
    simp only [M.bind_app, unpackSingle_live st self ptr fmt hL.live]

theorem indexItem_proven : IndexItem := by
  intro st self i n d f fmt hL hf
  have hnd : ¬ (st.mv self).view.ndim = 0 := by rw [hL.ndim]; omega
  have hsub : memorySubscript self (.one (.obj (.int i))) st =
      match keyAsSsize (.int i) i with
      | .error e => (.error e, st)
      | .ok index =>
        match memoryItem self index st with
        | (.ok x, s) => (.ok (.item x), s)
        | (.error e, s) => (.error e, s) := by
    simp only [memorySubscript, M.bind_app, checkReleased_ok _ _ hL.live, M.get, hnd, ↓reduceIte,
      Obj.isIndex, numberIndex, M.pure_app, M.lift]
    cases keyAsSsize (.int i) i with
    | error e => rfl
    | ok a =>
      simp only
      rcases memoryItem self a st with ⟨r, s⟩
      cases r <;> rfl
  dsimp only
  by_cases hs : ssizeMin ≤ i ∧ i ≤ ssizeMax
  · have hk : keyAsSsize (.int i) i = .ok i := by simp [keyAsSsize, hs]
    rw [hsub, hk]
    simp only [memoryItem_eq st self i n d f fmt hL hf]
    by_cases hin : -n ≤ i ∧ i < n
    · rw [lookup_in _ _ _ i n d hL.shape hL.strides hin]
      simp only
      cases hu : unpackRaw st.mem
          (adjustPtr st.mem ((st.mv self).view.buf + d * pos i n) (st.mv self).view.suboffsets 0) fmt with
      | error e =>
        refine ⟨rfl, fun h => absurd hs h, fun _ _ _ _ => rfl, fun _ _ h => absurd hin h⟩
      | ok x =>
        refine ⟨rfl, fun h => absurd hs h, fun _ _ _ _ => rfl, fun _ _ h => absurd hin h⟩
    · rw [lookup_out _ _ _ i n hL.shape hin]
      exact ⟨rfl, fun h => absurd hs h, fun _ _ h1 h2 => absurd ⟨h1, h2⟩ hin, fun _ _ _ => rfl⟩
  · have hk : keyAsSsize (.int i) i = .error (.indexError "cannot fit 'int' into an index-sized integer") := by
      simp [keyAsSsize, hs, Obj.typeName, toString]
    rw [hsub, hk]
    exact ⟨rfl, fun _ => rfl, fun h1 h2 => absurd ⟨h1, h2⟩ hs, fun h1 h2 => absurd ⟨h1, h2⟩ hs⟩

/-- A write that misses the pointer of a suboffset leaves the item's address alone. -/
theorem adjustPtr_write (m : Mem) (a : Int) (bs : List Nat) (p : Int) (subs : Option (List Int))
    (ha : 0 ≤ a) (hp : subs.isSome = true → 0 ≤ p ∧ (p + 8 ≤ a ∨ a + bs.length ≤ p)) :
    adjustPtr (wrBytes m a bs) p subs 0 = adjustPtr m p subs 0 := by
  have hr : ∀ (n : Nat) (q : Int), 0 ≤ q → q + n ≤ a ∨ a + bs.length ≤ q →
      rdBytes (wrBytes m a bs) q n = rdBytes m q n := by
    intro n
    induction n with
    | zero => intro _ _ _; rfl
    | succ n ih =>
      intro q h0 h1
      simp only [rdBytes]
      rw [rdByte_wrBytes_out _ _ _ _ ha h0 (by omega), ih (q + 1) (by omega) (by omega)]
  cases hs : subs with
  | none => rfl
  | some l =>
    simp only [adjustPtr]
    split
    · obtain ⟨h0, h1⟩ := hp (by simp [hs])
      simp only [rdU]
      rw [hr 8 p h0 (by omega)]
    · rfl

/-- `m[i] = v; m[i]` gives `v` back for a 1-D writable view of a native integer format, for every
in-range index and every in-range value, with or without a suboffset, and no byte outside the item
changes. Hypotheses: a live view whose item lies in the store; on a view with a suboffset, the
item does not overlap the pointer that leads to it. -/
def AssItemInt : Prop :=
  ∀ (st : St) (self : Nat) (i n d : Int) (f : List Char) (c : Char) (lo hi v : Int) (k : Nat),
    Live1D st self n d f → adjustFmt (st.mv self).view = .ok [c] →
    (st.mv self).view.readonly = false → intRange c = some (lo, hi, k) →
    ssizeMin ≤ i → i ≤ ssizeMax → -n ≤ i → i < n → lo ≤ v → v ≤ hi →
    let base := (st.mv self).view.buf + d * pos i n
    let addr := adjustPtr st.mem base (st.mv self).view.suboffsets 0
    0 ≤ addr → addr + k ≤ st.mem.length →
    ((st.mv self).view.suboffsets.isSome = true → 0 ≤ base ∧ (base + 8 ≤ addr ∨ addr + k ≤ base)) →
    let r := memoryAssSub self (.one (.obj (.int i))) (some (.int v)) st
    r.1 = .ok () ∧ (memorySubscript self (.one (.obj (.int i))) r.2).1 = .ok (.item (.int v)) ∧
    ∀ q, 0 ≤ q → q + 1 ≤ addr ∨ addr + k ≤ q → rdByte r.2.mem q = rdByte st.mem q

theorem assItemInt_proven : AssItemInt := by
  intro st self i n d f c lo hi v k hL hf hro hc h1 h2 h3 h4 h5 h6
  intro base addr ha hb hsep
  have hnd : ¬ (st.mv self).view.ndim = 0 := by rw [hL.ndim]; omega
  have hnd1 : ¬ 1 < (st.mv self).view.ndim := by rw [hL.ndim]; omega
  have hs : ssizeMin ≤ i ∧ i ≤ ssizeMax := ⟨h1, h2⟩
  have hk : keyAsSsize (.int i) i = .ok i := by simp [keyAsSsize, hs]
  have hass : memoryAssSub self (.one (.obj (.int i))) (some (.int v)) st =
      (.ok (), { st with mem := wrBytes st.mem addr (encInt v k) }) := by
    simp only [memoryAssSub, M.bind_app, checkReleased_ok _ _ hL.live, M.get, M.lift, hf, hro,
      Bool.false_eq_true, ↓reduceIte, hnd, Obj.isIndex, hnd1, numberIndex, M.pure_app, hk,
      ptrFromIndex, lookup_in _ _ _ i n d hL.shape hL.strides ⟨h3, h4⟩]
    exact pack_int_ok st self addr v lo hi c k hc hL.live ⟨h5, h6⟩
  dsimp only
  rw [hass]
  refine ⟨rfl, ?_, ?_⟩
  · have hL' : Live1D { st with mem := wrBytes st.mem addr (encInt v k) } self n d f :=
      { valid := hL.valid, mbuf := hL.mbuf, live := hL.live, unres := hL.unres, ndim := hL.ndim,
        shape := hL.shape, strides := hL.strides, subs := hL.subs, format := hL.format,
        nonneg := hL.nonneg, bound := hL.bound, span := hL.span }
    have := (indexItem_proven _ self i n d f [c] hL' hf).2.2.1 h1 h2 h3 h4
    rw [this]
    have hadj : adjustPtr (wrBytes st.mem addr (encInt v k)) base (st.mv self).view.suboffsets 0 = addr :=
      adjustPtr_write st.mem addr _ base _ ha (fun h => by simpa [encInt_length] using hsep h)
    show Sub.item <$> unpackRaw (wrBytes st.mem addr (encInt v k))
      (adjustPtr (wrBytes st.mem addr (encInt v k)) base (st.mv self).view.suboffsets 0) [c] = _
    rw [hadj, unpack_after_pack st.mem addr v lo hi c k hc ha hb ⟨h5, h6⟩]
    rfl
  · intro q hq hout
    exact rdByte_wrBytes_out _ _ _ _ ha hq (by rw [encInt_length]; omega)

/-- The rejected subscripts, each with its message, for every view with a single-character
format: a 0-dim view takes only `()` and `...`; `m[i]` on two or more dimensions, a tuple
of the wrong length, a tuple of slices, and anything that is not an index or slice are
refused (memoryobject.c:2588-2639). Hypotheses: a live view. -/
def KeyRejections : Prop :=
  ∀ (st : St) (self : Nat) (fmt : List Char),
    baseInaccessible st self = false → adjustFmt (st.mv self).view = .ok fmt →
    let v := (st.mv self).view
    (v.ndim = 0 → (∀ o, (memorySubscript self (.one (.obj o)) st).1 =
        .error (.typeError "invalid indexing of 0-dim memory")) ∧
      (memorySubscript self .ellipsis st).1 = .ok (.view self)) ∧
    (v.ndim ≠ 0 → (memorySubscript self .ellipsis st).1 =
        .error (.typeError "memoryview: invalid slice key")) ∧
    (2 ≤ v.ndim → ∀ i, ssizeMin ≤ i → i ≤ ssizeMax →
      (memorySubscript self (.one (.obj (.int i))) st).1 =
        .error (notImplError "multi-dimensional sub-views are not implemented")) ∧
    (v.ndim ≠ 0 → ∀ s, (memorySubscript self (.one (.obj (.str s))) st).1 =
        .error (.typeError "memoryview: invalid slice key")) ∧
    (v.ndim ≠ 0 → ∀ (es : List KeyElem), es ≠ [] → isMultislice es = true →
      (memorySubscript self (.tuple es) st).1 =
        .error (notImplError "multi-dimensional slicing is not implemented")) ∧
    (v.ndim ≠ 0 → ∀ (es : List KeyElem), isMultiindex es = true → es.length < v.ndim →
      (memorySubscript self (.tuple es) st).1 = .error (notImplError "sub-views are not implemented"))

theorem isMultislice_not_index (es : List KeyElem) (h : es ≠ []) (hs : isMultislice es = true) :
    isMultiindex es = false := by
  cases es with
  | nil => exact absurd rfl h
  | cons e es =>
    simp only [isMultislice, List.isEmpty_cons, Bool.not_false, Bool.true_and, List.all_cons,
      Bool.and_eq_true] at hs
    cases e with
    | obj o => simp at hs
    | slice s r => simp [isMultiindex]

theorem keyRejections_proven : KeyRejections := by
  intro st self fmt hl hf
  have hc := checkReleased_ok st self hl
  dsimp only
  have hsub0 : ∀ (hz : (st.mv self).view.ndim = 0) (k : Key), memorySubscript self k st =
      (match k with
       | .tuple [] => (do
          let fmt ← M.lift (adjustFmt (st.mv self).view)
          return Sub.item (← unpackSingle self (st.mv self).view.buf fmt)) st
       | .ellipsis => (.ok (.view self), st)
       | _ => (.error (.typeError "invalid indexing of 0-dim memory"), st)) := by
    intro hz k
    simp only [memorySubscript, M.bind_app, hc, M.get, hz, ↓reduceIte]
    cases k with
    | one e => rfl
    | ellipsis => rfl
    | tuple es =>
      cases es <;> rfl
  have hsubN : ∀ (hz : ¬ (st.mv self).view.ndim = 0) (k : Key), memorySubscript self k st =
      (match k with
       | .one (.obj o) =>
         if o.isIndex = true then (do
           let n ← numberIndex o
           let index ← M.lift (keyAsSsize o n)
           return Sub.item (← memoryItem self index)) st
         else (.error (.typeError "memoryview: invalid slice key"), st)
       | .tuple es =>
         if isMultiindex es = true then (do return Sub.item (← memoryItemMulti self es)) st
         else if isMultislice es = true then
           (.error (notImplError "multi-dimensional slicing is not implemented"), st)
         else (.error (.typeError "memoryview: invalid slice key"), st)
       | .ellipsis => (.error (.typeError "memoryview: invalid slice key"), st)
       | k => memorySubscript self k st) := by
    intro hz k
    cases k with
    | one e =>
      cases e with
      | obj o =>
        simp only [memorySubscript, M.bind_app, hc, M.get, hz, ↓reduceIte]
        by_cases h : o.isIndex = true <;> simp [h, M.throw_app, M.bind_app]
      | slice s r => rfl
    | ellipsis =>
      simp only [memorySubscript, M.bind_app, hc, M.get, hz, ↓reduceIte, M.throw_app]
    | tuple es =>
      simp only [memorySubscript, M.bind_app, hc, M.get, hz, ↓reduceIte]
      by_cases h1 : isMultiindex es = true
      · simp only [h1, ↓reduceIte, M.bind_app, M.pure_app]
      · by_cases h2 : isMultislice es = true <;> simp [h1, h2, M.throw_app, M.bind_app]
  refine ⟨fun hz => ⟨fun o => ?_, ?_⟩, fun hz => ?_, fun hd i h1 h2 => ?_, fun hz s => ?_,
    fun hz es hne hs => ?_, fun hz es hm hlen => ?_⟩
  · rw [hsub0 hz]
  · rw [hsub0 hz]
  · rw [hsubN hz]
  · have hz : ¬ (st.mv self).view.ndim = 0 := by omega
    have hk : keyAsSsize (.int i) i = .ok i := by simp [keyAsSsize, h1, h2]
    have hne1 : ¬ (st.mv self).view.ndim = 1 := by omega
    rw [hsubN hz]
    simp only [Obj.isIndex, ↓reduceIte, M.bind_app, numberIndex, M.pure_app, M.lift, hk, memoryItem, hc,
      M.get, hf, hz, hne1, M.throw_app]
  · have hz' : ¬ (st.mv self).view.ndim = 0 := hz
    rw [hsubN hz']
    simp [Obj.isIndex]
  · have hz' : ¬ (st.mv self).view.ndim = 0 := hz
    rw [hsubN hz']
    simp [isMultislice_not_index es hne hs, hs]
  · have hz' : ¬ (st.mv self).view.ndim = 0 := hz
    rw [hsubN hz']
    simp only [hm, ↓reduceIte, M.bind_app, memoryItemMulti, hc, M.get, M.lift, hf, M.pure_app, hlen,
      M.throw_app]

end PyLean.BytesObj.Mem
