import PyLean.BytesObj.Mem.Release

/-!
Refutations on concrete views, and the properties that remain true once the refuted cases
are excluded. Each refuted property has a `bugs/bytesobj-memoryview-*.yaml` record.
-/

namespace PyLean.BytesObj.Mem

open PyLean
open PyLean.RangeSlice (Slice sliceUnpack adjustIndices)

/-- A view of `n` items of size `size` at address 0, format `f`. -/
def fmtBuf (n size : Int) (f : List Char) : Buf :=
  { obj := some (.exp 0), buf := 0, len := n * size, itemsize := size, readonly := false, ndim := 1,
    format := some f, shape := some [n], strides := some [size] }

/-- One managed buffer, one view (number 0). -/
def stateOf (m : Mem) (b : Buf) : St :=
  { mem := m, mbufs := [{ master := b, exports := 1 }], mvs := [{ view := b, flags := initFlags b }],
    unhashable := [none] }

/-! ## A release in `__index__` of the key -/

/-- `m[k] = v` with an `__index__` of `k` that releases `m`: nothing may be written, since
the buffer may be gone (gh-92888 and `test_use_released_memory`). Quantified over every view
that has no exports, so that the callback's `release()` succeeds. -/
def ReleasedKeyNoWrite : Prop :=
  ∀ (st : St) (self : Nat) (n : Int) (v : Obj),
    self < st.mvs.length → (st.mv self).exports = 0 →
    (memoryAssSub self (.one (.obj (.index (.val n) (some self)))) (some v) st).2.mem = st.mem

/-- `m = memoryview(bytearray(8)).cast('c'); m[K()] = b'x'` writes: the arm for `c` of
`pack_single` has no `CHECK_RELEASED_INT_AGAIN`, and `memory_ass_sub` took the pointer
after the callback ran (with `ba.clear()` in `__index__`, a write to freed memory). -/
theorem releasedKeyNoWrite_refuted : ¬ ReleasedKeyNoWrite := by
  intro h
  have := h (stateOf [97, 97] (fmtBuf 2 1 ['c'])) 0 0 (.bytes [120]) (by decide) rfl
  have e : (memoryAssSub 0 (.one (.obj (.index (.val 0) (some 0)))) (some (.bytes [120]))
      (stateOf [97, 97] (fmtBuf 2 1 ['c']))).2.mem = [120, 97] := by rfl
  rw [e] at this
  exact absurd this (by decide)

theorem fire_bind_mono {α : Type} (r : Option Nat) (f : PUnit → M α) (st : St)
    (hf : ∀ s, Mono s (f () s).2) : Mono st ((fire r >>= f) st).2 := by
  rw [M.bind_app]
  have h := fire_mono r st
  rcases hx : fire r st with ⟨res, s⟩
  rw [hx] at h
  cases res with
  | error e => exact h
  | ok a => exact h.trans (hf s)

theorem get_mono {α : Type} (w : String → PyExc) (r : Ret α) (st : St) : Mono st (r.get w st).2 := by
  rw [Ret.get_state]
  exact Mono.refl _

theorem numberIndex_mono (o : Obj) (st : St) : Mono st (numberIndex o st).2 := by
  cases o
  case index n rel => exact fire_bind_mono rel _ st fun s => get_mono _ _ s
  all_goals exact Mono.refl _

theorem lift_bind_mono {α β : Type} (x : M α) (f : α → Py β) (st : St)
    (h : Mono st (x st).2) : Mono st ((x >>= fun a => M.lift (f a)) st).2 := by
  rw [M.bind_app]
  rcases hx : x st with ⟨r, s⟩
  rw [hx] at h
  cases r with
  | error e => exact h
  | ok a => exact h

theorem floatAsDouble_mono (o : Obj) (st : St) : Mono st (floatAsDouble o st).2 := by
  cases o
  case index n rel =>
    exact fire_bind_mono rel _ st fun s => lift_bind_mono _ _ s (get_mono _ _ s)
  case floatLike b rel => exact fire_bind_mono rel _ st fun s => get_mono _ _ s
  all_goals exact Mono.refl _

theorem isTrue_mono (o : Obj) (st : St) : Mono st (isTrue o st).2 := by
  cases o
  case boolLike b rel => exact fire_bind_mono rel _ st fun s => get_mono _ _ s
  case view i =>
    simp only [isTrue, M.bind_app, M.get]
    cases h : baseInaccessible st i
    · simp only [checkReleased_ok _ _ h]
      by_cases hz : (st.mv i).view.ndim = 0
      · simp only [hz, ↓reduceIte, M.bind_app, M.throw_app]
        exact Mono.refl _
      · simp only [hz, ↓reduceIte, M.pure_app]
        exact Mono.refl _
    · simp only [checkReleased_err _ _ h]
      exact Mono.refl _
  all_goals exact Mono.refl _

theorem mapErr_snd {α : Type} (f : PyExc → PyExc) (x : M α) (st : St) :
    (M.mapErr f x st).2 = (x st).2 := by
  simp only [M.mapErr]
  rcases x st with ⟨r, s⟩
  cases r <;> rfl

/-- Converting the item, then `CHECK_RELEASED_INT_AGAIN`: nothing after the check runs. -/
theorem conv_check {α β : Type} (x : M α) (self : Nat) (f : α → Unit → M β) (st : St)
    (hx : Mono st (x st).2) (h : baseInaccessible st self = true) :
    ((x >>= fun a => checkReleased self >>= f a) st).2.mem = st.mem := by
  rw [M.bind_app]
  rcases hs : x st with ⟨r, s⟩
  rw [hs] at hx
  simp only at hx
  cases r with
  | error e => exact hx.mem
  | ok a =>
    simp only
    rw [bind_err _ _ _ _ _ (checkReleased_err s self (hx.inaccessible self h))]
    exact hx.mem

theorem conv_check' {α β : Type} (x : M α) (self : Nat) (f : Unit → M β) (st : St)
    (g : α → M β) (hg : g = fun _ => checkReleased self >>= f)
    (hx : Mono st (x st).2) (h : baseInaccessible st self = true) :
    ((x >>= g) st).2.mem = st.mem := by
  subst hg
  exact conv_check x self (fun _ => f) st hx h

theorem pylong_mono (y : M Int) (f : Int → Py Int) (c : List Char)
    (hy : ∀ s, Mono s (y s).2) (s : St) :
    Mono s (M.mapErr (fixErrorInt c) (do M.lift (f (← y))) s).2 := by
  rw [mapErr_snd]
  exact lift_bind_mono y f s (hy s)

/-- A released view is never written, by any format but `c`, whatever the item and its
conversion callbacks. -/
theorem pack_released_nowrite (st : St) (self : Nat) (ptr : Int) (item : Obj) (c : Char)
    (hc : c ≠ 'c') (h : baseInaccessible st self = true) :
    (packSingle self ptr item [c] st).2.mem = st.mem := by
  have hN := numberIndex_mono item
  have hL : ∀ (f : Int → Py Int) s, Mono s (M.mapErr (fixErrorInt [c]) (do M.lift (f (← numberIndex item))) s).2 :=
    fun f s => pylong_mono _ f _ hN s
  unfold packSingle
  simp only [cc, List.getD_cons_zero]
  split
  all_goals first
    | exact conv_check _ self _ st (hL _ st) h
    | exact conv_check _ self _ st (by rw [mapErr_snd]; exact floatAsDouble_mono item st) h
    | exact conv_check _ self _ st (isTrue_mono item st) h
    | exact conv_check _ self _ st (by rw [mapErr_snd]; exact Mono.refl _) h
    | rfl
    | contradiction

theorem memoryRelease_inaccessible (i : Nat) (st : St) (hi : i < st.mvs.length) :
    baseInaccessible (memoryRelease i st).2 i = true := by
  by_cases hr : (st.mv i).flags.released = true
  · have : memoryRelease i st = (.ok (), st) := by simp [memoryRelease, hr]
    rw [this]
    simp [baseInaccessible, hr]
  · unfold memoryRelease
    simp only [hr, Bool.false_eq_true, ↓reduceIte]
    generalize hy : ({ st.mv i with flags := { (st.mv i).flags with released := true } } : MV) = y
    have hmv : (st.setMv i y).mv i = y := St.mv_setMv _ _ _ hi
    have hyr : y.flags.released = true := by rw [← hy]
    have h1 : baseInaccessible (St.setMb (st.setMv i y) (st.mv i).mbuf
        { (st.setMv i y).mb (st.mv i).mbuf with
          exports := ((st.setMv i y).mb (st.mv i).mbuf).exports - 1 }) i = true := by
      simp [baseInaccessible, hmv, hyr]
    split
    · exact (mbufRelease_mono _ _).inaccessible i h1
    · exact h1

/-- The property above with the format `c` taken out: for every other format, whatever the
item, a release during the key's `__index__` means nothing is written. -/
def ReleasedKeyNoWriteNotC : Prop :=
  ∀ (st : St) (self : Nat) (n : Int) (v : Obj) (c : Char),
    self < st.mvs.length → (st.mv self).exports = 0 → c ≠ 'c' →
    adjustFmt (st.mv self).view = .ok [c] →
    (memoryAssSub self (.one (.obj (.index (.val n) (some self)))) (some v) st).2.mem = st.mem

theorem releasedKeyNoWriteNotC_proven : ReleasedKeyNoWriteNotC := by
  intro st self n v c hs hexp hc hf
  cases hi : baseInaccessible st self
  · simp only [memoryAssSub, M.bind_app, checkReleased_ok _ _ hi, M.get, M.lift, hf]
    by_cases hro : (st.mv self).view.readonly = true
    · simp [hro, M.bind_app, M.throw_app]
    · by_cases h0 : (st.mv self).view.ndim = 0
      · simp [hro, h0, M.bind_app, M.throw_app]
      · by_cases h1 : 1 < (st.mv self).view.ndim
        · simp [hro, h0, h1, Obj.isIndex, M.bind_app, M.throw_app]
        · have hfire : fire (some self) st = memoryRelease self st := by
            show (if getExports st self = 0 then memoryRelease self st else (.ok (), st)) = _
            simp [getExports, hexp]
          have hm := memoryRelease_mono self st
          have hin := memoryRelease_inaccessible self st hs
          rcases hr : memoryRelease self st with ⟨res, s1⟩
          rw [hr] at hm hin
          simp only at hm hin
          have hmem : s1.mem = st.mem := hm.mem
          simp only [hro, h0, h1, Obj.isIndex, Bool.false_eq_true, ↓reduceIte, M.bind_app, numberIndex,
            hfire, hr, M.pure_app, M.get, M.lift]
          cases res with
          | error e => exact hmem
          | ok u =>
            simp only [M.bind_app, M.get, M.pure_app, M.lift, Ret.get_val]
            cases hk : keyAsSsize (.index (.val n) (some self)) n with
            | error e => simpa using hmem
            | ok index =>
              simp only [hk]
              cases hp : ptrFromIndex s1.mem (st.mv self).view index with
              | error e => simpa using hmem
              | ok ptr =>
                simp only
                rw [pack_released_nowrite s1 self ptr v c hc hin, hmem]
  · simp only [memoryAssSub, M.bind_app, checkReleased_err _ _ hi]

/-! ## A release in `__buffer__` of the other operand -/

/-- A view released while `==` obtains the other operand's buffer compares like a released
view: by identity (:3113-3116), so not equal to that operand. Quantified over all views
with no exports and all exporters of at most 64 dimensions. -/
def CmpReleasedIdentity : Prop :=
  ∀ (st : St) (v : Nat) (b : Buf),
    v < st.mvs.length → (st.mv v).exports = 0 → b.ndim ≤ 64 →
    (memoryRichcompare v (.exporter (.val b) (some v)) .eq st).1 = .ok (some false)

/-- `m == W()` with a `__buffer__` that does `m.release()` compares the released memory. -/
theorem cmpReleasedIdentity_refuted : ¬ CmpReleasedIdentity := by
  intro h
  have := h (stateOf [97] (fmtBuf 1 1 ['B'])) 0 (fmtBuf 1 1 ['B']) (by decide) rfl (by decide)
  have e : (memoryRichcompare 0 (.exporter (.val (fmtBuf 1 1 ['B'])) (some 0)) .eq
      (stateOf [97] (fmtBuf 1 1 ['B']))).1 = .ok (some true) := by rfl
  rw [e] at this
  exact absurd this (by decide)

/-! ## Contiguity of an empty strided view -/

/-- `m.c_contiguous` is what `PyBuffer_IsContiguous(view, 'C')` says, for every 1-D view:
the fast test `MV_CONTIGUOUS_NDIM1` of `init_flags` and the general one are the same
property. -/
def Ndim1ContigAgree : Prop :=
  ∀ (v : Buf) (n d : Int), v.ndim = 1 → v.suboffsets = none → v.shape = some [n] →
    v.strides = some [d] → v.len = n * v.itemsize → 0 ≤ n → 0 < v.itemsize →
    (initFlags v).isC = pyBufferIsContiguous v 'C'

/-- `memoryview(b'abc')[1:1:2]`: an empty view with stride 2 is contiguous for
`PyBuffer_IsContiguous` ("len = 0" comes first) and not for `MV_CONTIGUOUS_NDIM1`. -/
theorem ndim1ContigAgree_refuted : ¬ Ndim1ContigAgree := by
  intro h
  have := h { buf := 1, len := 0, itemsize := 1, ndim := 1, format := some ['B'],
              shape := some [0], strides := some [2] } 0 2 rfl rfl rfl rfl (by decide) (by decide)
    (by decide)
  exact absurd this (by decide)

/-- The same for every non-empty view, in both orders: the fast test is right there. -/
def Ndim1ContigNonempty : Prop :=
  ∀ (v : Buf) (n d : Int), v.ndim = 1 → v.suboffsets = none → v.shape = some [n] →
    v.strides = some [d] → v.len = n * v.itemsize → 0 < n → 0 < v.itemsize →
    (initFlags v).isC = pyBufferIsContiguous v 'C' ∧
    (initFlags v).isF = pyBufferIsContiguous v 'F'

theorem ndim1ContigNonempty_proven : Ndim1ContigNonempty := by
  intro v n d h1 hs hsh hst hl hn hi
  have hlen : v.len ≠ 0 := by
    rw [hl]
    exact Int.ne_of_gt (Int.mul_pos hn hi)
  have hflags : initFlags v = if mvContiguousNdim1 v = true then { c := true, fortran := true } else {} := by
    unfold initFlags
    rw [h1, hs]
    rfl
  have hm : mvContiguousNdim1 v = (n == 1 || d == v.itemsize) := by
    simp [mvContiguousNdim1, hsh, hst]
  by_cases hc : n = 1 ∨ d = v.itemsize
  · have htrue : mvContiguousNdim1 v = true := by
      rw [hm]
      rcases hc with h | h <;> simp [h]
    rw [hflags, htrue]
    constructor
    · simp only [↓reduceIte, Flags.isC, pyBufferIsContiguous, hs, isCContiguous, hlen, hst, hsh, h1,
        Option.isSome_none, cLoop]
      rcases hc with h | h <;> simp [h]
    · simp only [↓reduceIte, Flags.isF, pyBufferIsContiguous, hs, isFortranContiguous, hlen, hst, hsh,
        Option.isSome_none, fLoop]
      rcases hc with h | h <;> simp [h, fLoop]
  · have hn1 : n ≠ 1 := fun e => hc (Or.inl e)
    have hd : d ≠ v.itemsize := fun e => hc (Or.inr e)
    have hfalse : mvContiguousNdim1 v = false := by
      rw [hm]
      simp [hn1, hd]
    have hgt : n > 1 := by omega
    rw [hflags, hfalse]
    constructor
    · simp [Flags.isC, pyBufferIsContiguous, hs, isCContiguous, hlen, hst, hsh, h1, cLoop, hd, hgt]
    · simp [Flags.isF, pyBufferIsContiguous, hs, isFortranContiguous, hlen, hst, hsh, fLoop, hd, hgt]

/-! ## `__buffer__` without `PyBUF_FORMAT` -/

/-- `struct.calcsize(m.format) == m.itemsize` (Doc/library/stdtypes.rst, `itemsize`) survives
`m.__buffer__(flags)`, for every view of a native format and all flags. -/
def BufferKeepsItemsize : Prop :=
  ∀ (st st' : St) (self : Nat) (flags i : Nat) (c : Char) (size : Int),
    getNativeFmtchar ((st.mv self).view.format.getD []) = some (c, size) →
    (st.mv self).view.itemsize = size →
    memoryBufferProc self flags st = (.ok i, st') →
    getNativeFmtchar ((st'.mv i).view.format.getD []) = some (c, size)

/-- `memoryview(array('i', [1])).__buffer__(0)` has format `B` and itemsize 4:
`memory_getbuf` drops the format ("the buffer's data type has been cast to 'B'", :1548) and
keeps the item size; `mbuf_add_view` then fills in `"B"` (:550). -/
theorem bufferKeepsItemsize_refuted : ¬ BufferKeepsItemsize := by
  intro h
  have := h (stateOf [1, 0, 0, 0] (fmtBuf 1 4 ['i'])) _ 0 0 1 'i' 4 rfl rfl
    (show _ = ((memoryBufferProc 0 0 (stateOf [1, 0, 0, 0] (fmtBuf 1 4 ['i']))).1,
               (memoryBufferProc 0 0 (stateOf [1, 0, 0, 0] (fmtBuf 1 4 ['i']))).2) from rfl)
  exact absurd this (by decide)

/-! ## `init_slice` -/

/-- The stride of `m[::k]` is `m.strides[0] * k`, for every step, with no `Py_ssize_t`
overflow in `init_slice`. -/
def SliceStrideExact : Prop :=
  ∀ (v : Buf) (s : Slice) (w : Buf) (d start stop step : Int),
    v.strides = some [d] → sliceUnpack s = .ok (start, stop, step) →
    initSlice v s 0 = .ok w → w.strides = some [d * step]

/-- `memoryview(bytes(16)).cast('q')[::sys.maxsize].strides == (-8,)`: the product wraps
(`base->strides[dim] * step` at :2532 is signed overflow). -/
theorem sliceStrideExact_refuted : ¬ SliceStrideExact := by
  intro h
  have := h (fmtBuf 2 8 ['q']) ⟨none, none, some ssizeMax⟩
    { fmtBuf 2 8 ['q'] with shape := some [1], strides := some [-8] } 8 0 ssizeMax ssizeMax
    rfl rfl rfl
  exact absurd this (by decide)

end PyLean.BytesObj.Mem
