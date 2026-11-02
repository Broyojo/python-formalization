import PyLean.BytesObj.Mem.Fortran

/-!
What the C code refuses, and with which message. The theorems that describe success take these
checks as hypotheses, so a function that always refuses, or never does, passes those; here each
refusal is stated, with its order, and the success beside it.
-/

namespace PyLean.BytesObj.Mem

open PyLean

/-! ## `memory_getbuf` -/

/-- `memory_getbuf` on the view's own description, for every flag set: each refusal with its
message, in the order of @3.14.7:1538-1599, and when none applies the copy with the fields the flags ask
for. PyBUF_SIMPLE on a C-contiguous view succeeds with no format, no strides and no shape;
PyBUF_FULL_RO on any view succeeds unless nothing else does. -/
def GetbufOrder : Prop :=
  ∀ (base : Buf) (f : Flags) (flags : Nat),
    let view := viewFormat flags { base with obj := none }
    let a1 := (flags &&& bufWritable) != 0 && base.readonly
    let a2 := req flags bufCContiguous && !f.isC
    let a3 := req flags bufFContiguous && !f.isF
    let a4 := req flags bufAnyContiguous && !f.isAny
    let a5 := !req flags bufIndirect && f.pil
    let a6 := !req flags bufStrides && !f.isC
    let a7 := !req flags bufND && (viewStrides flags view).format.isSome
    (a1 = true → getbufView base f flags =
      .error (.named "BufferError" "memoryview: underlying buffer is not writable")) ∧
    (a1 = false → a2 = true → getbufView base f flags =
      .error (.named "BufferError" "memoryview: underlying buffer is not C-contiguous")) ∧
    (a1 = false → a2 = false → a3 = true → getbufView base f flags =
      .error (.named "BufferError" "memoryview: underlying buffer is not Fortran contiguous")) ∧
    (a1 = false → a2 = false → a3 = false → a4 = true → getbufView base f flags =
      .error (.named "BufferError" "memoryview: underlying buffer is not contiguous")) ∧
    (a1 = false → a2 = false → a3 = false → a4 = false → a5 = true → getbufView base f flags =
      .error (.named "BufferError" "memoryview: underlying buffer requires suboffsets")) ∧
    (a1 = false → a2 = false → a3 = false → a4 = false → a5 = false → a6 = true →
      getbufView base f flags =
        .error (.named "BufferError" "memoryview: underlying buffer is not C-contiguous")) ∧
    (a1 = false → a2 = false → a3 = false → a4 = false → a5 = false → a6 = false → a7 = true →
      getbufView base f flags =
        .error (.named "BufferError" "memoryview: cannot cast to unsigned bytes if the format flag is present")) ∧
    (a1 = false → a2 = false → a3 = false → a4 = false → a5 = false → a6 = false → a7 = false →
      getbufView base f flags = .ok (viewShape flags (viewStrides flags view)))

theorem nt {x : Bool} (h : x = false) : ¬ x = true := by simp [h]

theorem getbufOrder_proven : GetbufOrder := by
  intro base f flags
  dsimp only
  unfold getbufView
  dsimp only
  refine ⟨fun h1 => ?_, fun h1 h2 => ?_, fun h1 h2 h3 => ?_, fun h1 h2 h3 h4 => ?_, fun h1 h2 h3 h4 h5 => ?_,
    fun h1 h2 h3 h4 h5 h6 => ?_, fun h1 h2 h3 h4 h5 h6 h7 => ?_, fun h1 h2 h3 h4 h5 h6 h7 => ?_⟩
  · rw [if_pos h1]; rfl
  · rw [if_neg (nt h1), if_pos h2]; rfl
  · rw [if_neg (nt h1), if_neg (nt h2), if_pos h3]; rfl
  · rw [if_neg (nt h1), if_neg (nt h2), if_neg (nt h3), if_pos h4]; rfl
  · rw [if_neg (nt h1), if_neg (nt h2), if_neg (nt h3), if_neg (nt h4), if_pos h5]; rfl
  · rw [if_neg (nt h1), if_neg (nt h2), if_neg (nt h3), if_neg (nt h4), if_neg (nt h5), if_pos h6]; rfl
  · rw [if_neg (nt h1), if_neg (nt h2), if_neg (nt h3), if_neg (nt h4), if_neg (nt h5), if_neg (nt h6),
      if_pos h7]; rfl
  · rw [if_neg (nt h1), if_neg (nt h2), if_neg (nt h3), if_neg (nt h4), if_neg (nt h5), if_neg (nt h6),
      if_neg (nt h7)]

/-- What `getbufView` says is what `memory_getbuf` does, for a live, unrestricted view: a refusal
changes nothing, and a success counts one export and hands out the view as `obj`. -/
def GetbufLift : Prop :=
  ∀ (st : St) (self flags : Nat), self < st.mvs.length → baseInaccessible st self = false →
    (st.mv self).flags.restricted = false →
    let x := st.mv self
    (∀ e, getbufView x.view x.flags flags = .error e → memoryGetbuf self flags st = (.error e, st)) ∧
    (∀ b, getbufView x.view x.flags flags = .ok b →
      (memoryGetbuf self flags st).1 = .ok { b with obj := some (.mv self), hook := none } ∧
      ((memoryGetbuf self flags st).2.mv self).exports = x.exports + 1)

theorem getbufLift_proven : GetbufLift := by
  intro st self flags hi hl hr
  dsimp only
  have e1 := checkReleased_ok st self hl
  have e2 := checkRestricted_ok st self hr
  refine ⟨fun e h => ?_, fun b h => ?_⟩
  · simp [memoryGetbuf, M.bind_app, e1, e2, M.get, M.lift, h, M.throw_app]
  · simp [memoryGetbuf, M.bind_app, e1, e2, M.get, M.lift, h, M.pure_app, M.modify, St.mv_setMv _ _ _ hi]

/-! ## `copy_shape` -/

/-- The product of a shape. -/
def prodL : List Int → Int
  | [] => 1
  | x :: xs => x * prodL xs

/-- `copy_shape` for every element and every running product: an element that is no int, one that
does not fit a `Py_ssize_t`, one that is not positive, and a product past `SSIZE_MAX` are each refused
with their own message, in that order; a good shape gives its product, times the item size. -/
def CopyShapeRules : Prop :=
  (∀ (o : Obj) (rest : List Obj) (len : Int), o.asLong? = none →
    copyShape (o :: rest) len = .error (.typeError "memoryview.cast(): elements of shape must be integers")) ∧
  (∀ (v : Int) (rest : List Obj) (len : Int), v < ssizeMin ∨ v > ssizeMax →
    copyShape (.int v :: rest) len =
      .error (.overflowError "Python int too large to convert to C ssize_t")) ∧
  (∀ (v : Int) (rest : List Obj) (len : Int), ssizeMin ≤ v → v ≤ 0 →
    copyShape (.int v :: rest) len =
      .error (.valueError "memoryview.cast(): elements of shape must be integers > 0")) ∧
  (∀ (v : Int) (rest : List Obj) (len : Int), 0 < v → v ≤ ssizeMax → v > Int.tdiv ssizeMax len →
    copyShape (.int v :: rest) len =
      .error (.valueError "memoryview.cast(): product(shape) > SSIZE_MAX")) ∧
  (∀ (sh : List Int) (len : Int), 0 < len → (∀ x ∈ sh, 0 < x) → len * prodL sh ≤ ssizeMax →
    copyShape (sh.map .int) len = .ok (len * prodL sh, sh))

theorem prodL_pos : ∀ sh : List Int, (∀ x ∈ sh, 0 < x) → 1 ≤ prodL sh
  | [], _ => by simp [prodL]
  | x :: xs, h => by
    have h1 := h x (by simp)
    have h2 := prodL_pos xs fun y hy => h y (by simp [hy])
    simp only [prodL]
    exact Int.mul_pos h1 (by omega)

theorem copyShape_value : ∀ (sh : List Int) (len : Int), 0 < len → (∀ x ∈ sh, 0 < x) →
    len * prodL sh ≤ ssizeMax → copyShape (sh.map .int) len = .ok (len * prodL sh, sh)
  | [], len, _, _, _ => by simp [copyShape, prodL]
  | x :: xs, len, h0, hp, hm => by
    have hx := hp x (by simp)
    have hr := prodL_pos xs fun y hy => hp y (by simp [hy])
    have hle : len * x ≤ len * (x * prodL xs) := by
      apply Int.mul_le_mul_of_nonneg_left _ (by omega)
      have := Int.mul_le_mul_of_nonneg_left hr (show 0 ≤ x by omega)
      simpa using this
    simp only [prodL] at hm
    have h1 : x ≤ len * x := by
      have := Int.mul_le_mul_of_nonneg_right (show 1 ≤ len by omega) (show 0 ≤ x by omega)
      simpa using this
    have hs : ssizeMin ≤ x ∧ x ≤ ssizeMax := by
      unfold ssizeMin ssizeMax at *
      omega
    have ht : ¬ x > Int.tdiv ssizeMax len := by
      rw [Int.tdiv_eq_ediv_of_nonneg (by unfold ssizeMax; omega)]
      have : x ≤ ssizeMax / len := Int.le_ediv_of_mul_le h0 (by rw [Int.mul_comm]; omega)
      omega
    have ih := copyShape_value xs (len * x) (Int.mul_pos h0 (by omega))
      (fun y hy => hp y (by simp [hy])) (by rw [Int.mul_assoc]; exact hm)
    simp only [List.map_cons, copyShape, Obj.asLong?, longAsSsize, hs, and_self, ↓reduceIte, bind,
      Except.bind, show ¬ x ≤ 0 by omega, ht, pure, Except.pure]
    simp only [ih, Int.mul_assoc, prodL]

theorem copyShapeRules_proven : CopyShapeRules := by
  refine ⟨fun o rest len h => ?_, fun v rest len h => ?_, fun v rest len h1 h2 => ?_,
    fun v rest len h1 h2 h3 => ?_, copyShape_value⟩
  · simp [copyShape, h]
  · have : ¬ (ssizeMin ≤ v ∧ v ≤ ssizeMax) := by omega
    simp [copyShape, Obj.asLong?, longAsSsize, this, bind, Except.bind]
  · have hs : ssizeMin ≤ v ∧ v ≤ ssizeMax := ⟨h1, by unfold ssizeMax; omega⟩
    simp [copyShape, Obj.asLong?, longAsSsize, hs, h2, bind, Except.bind]
  · have hs : ssizeMin ≤ v ∧ v ≤ ssizeMax := ⟨by unfold ssizeMin; omega, h2⟩
    have h4 : ¬ v ≤ 0 := by omega
    simp [copyShape, Obj.asLong?, longAsSsize, hs, h4, h3, bind, Except.bind]

/-! ## `is_multislice` -/

/-- `is_multislice` is exactly "a non-empty tuple of slices"; with `is_multiindex`, the two sort a
tuple key into three arms, and each of the arms has its own answer in `memory_subscript` and in
`memory_ass_sub`. A stand-in that says false turns `m[1:2, 3:4]` into `TypeError`. -/
def MultisliceSpec : Prop :=
  ∀ (es : List KeyElem),
    (isMultislice es = true ↔ es ≠ [] ∧ ∀ e ∈ es, ∃ s r f, e = .slice s r f) ∧
    ∀ (st : St) (self : Nat), baseInaccessible st self = false →
      (st.mv self).view.ndim ≠ 0 → isMultiindex es = false →
      (memorySubscript self (.tuple es) st).1 =
        (if isMultislice es then .error (notImplError "multi-dimensional slicing is not implemented")
         else .error (.typeError "memoryview: invalid slice key"))

theorem multisliceSpec_proven : MultisliceSpec := by
  intro es
  constructor
  · simp only [isMultislice, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun e he => ?_⟩
      have := h2 e he
      cases e with
      | obj o => simp at this
      | slice s r f => exact ⟨s, r, f, rfl⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun e he => ?_⟩
      obtain ⟨s, r, f, rfl⟩ := h2 e he
      rfl
  · intro st self hl hn hi
    have e := checkReleased_ok st self hl
    simp only [memorySubscript, M.bind_app, e, M.get, hn, ↓reduceIte, hi, Bool.false_eq_true]
    split <;> rfl

/-! ## `cast_to_1D` -/

/-- What `cast_to_1D` refuses, in order, on the fresh view of a `cast`: a format with a non-ASCII
character, one that is no native single character, two non-byte formats, and a length that is no
multiple of the new item size. Each leaves the state alone. -/
def Cast1DRefusals : Prop :=
  ∀ (st : St) (i : Nat) (format : List Char),
    let view := (st.mv i).view
    (format.any (fun c => c.toNat ≥ 128) = true → castTo1D i format st = (.error unicodeEncodeError, st)) ∧
    (format.any (fun c => c.toNat ≥ 128) = false → getNativeFmtchar format = none →
      castTo1D i format st = (.error (.valueError
        "memoryview: destination format must be a native format prefixed with an optional '@'"), st)) ∧
    (∀ c size, format.any (fun c => c.toNat ≥ 128) = false → getNativeFmtchar format = some (c, size) →
      srcIsByte view = false → isByteFormat c = false →
      castTo1D i format st = (.error (.typeError "memoryview: cannot cast between two non-byte formats"), st)) ∧
    (∀ c size, format.any (fun c => c.toNat ≥ 128) = false → getNativeFmtchar format = some (c, size) →
      (srcIsByte view = true ∨ isByteFormat c = true) → view.len.tmod size ≠ 0 →
      castTo1D i format st = (.error (.typeError "memoryview: length is not a multiple of itemsize"), st))

theorem cast1DRefusals_proven : Cast1DRefusals := by
  intro st i format
  dsimp only
  refine ⟨fun h => ?_, fun h1 h2 => ?_, fun c size h1 h2 h3 h4 => ?_, fun c size h1 h2 h3 h4 => ?_⟩
  · simp [castTo1D, M.bind_app, M.get, h, M.throw_app]
  · simp [castTo1D, M.bind_app, M.get, h1, h2, M.throw_app]
  · simp [castTo1D, M.bind_app, M.get, h1, h2, h3, h4, M.throw_app]
  · have h5 : ¬ (srcIsByte (st.mv i).view = false ∧ isByteFormat c = false) := by
      rcases h3 with h | h <;> simp [h]
    simp [castTo1D, M.bind_app, M.get, h1, h2, h4, h5, M.throw_app]


/-! ## `memory_ass_sub` -/

/-- `m[key] = value` and `del m[key]`, for every live view and key, in the order of @3.14.7:2642-2743: a
format that is not one character, then read-only memory, then a deletion, then the shape of the key.
Each refusal leaves the state alone. A 0-dim view stores through `...` and `()` and nothing else; a
view of more dimensions stores through a full tuple of indices; `...` is refused there. -/
def AssSubRules : Prop :=
  ∀ (st : St) (self : Nat) (key : Key) (value : Obj), baseInaccessible st self = false →
    let v := (st.mv self).view
    (∀ (e : PyExc) (val : Option Obj), adjustFmt v = .error e → memoryAssSub self key val st = (.error e, st)) ∧
    (∀ (fmt : List Char), adjustFmt v = .ok fmt →
      (v.readonly = true → ∀ val : Option Obj, memoryAssSub self key val st =
        (.error (.typeError "cannot modify read-only memory"), st)) ∧
      (v.readonly = false → memoryAssSub self key none st =
        (.error (.typeError "cannot delete memory"), st)) ∧
      (v.readonly = false → v.ndim = 0 →
        memoryAssSub self .ellipsis (some value) st = packSingle self v.buf value fmt st ∧
        memoryAssSub self (.tuple []) (some value) st = packSingle self v.buf value fmt st ∧
        (∀ e, memoryAssSub self (.one e) (some value) st =
          (.error (.typeError "invalid indexing of 0-dim memory"), st))) ∧
      (v.readonly = false → v.ndim ≠ 0 →
        memoryAssSub self .ellipsis (some value) st =
          (.error (.typeError "memoryview: invalid slice key"), st) ∧
        (∀ es : List KeyElem, isMultiindex es = true → es.length < v.ndim →
          memoryAssSub self (.tuple es) (some value) st =
            (.error (notImplError "sub-views are not implemented"), st)) ∧
        (∀ es : List KeyElem, isMultiindex es = true → ¬ es.length < v.ndim →
          memoryAssSub self (.tuple es) (some value) st =
            (do let p ← ptrFromTuple v es; packSingle self p value fmt) st) ∧
        (∀ es : List KeyElem, isMultiindex es = false → isMultislice es = true →
          memoryAssSub self (.tuple es) (some value) st =
            (.error (notImplError "memoryview slice assignments are currently restricted to ndim = 1"), st)) ∧
        (∀ es : List KeyElem, isMultiindex es = false → isMultislice es = false →
          memoryAssSub self (.tuple es) (some value) st =
            (.error (.typeError "memoryview: invalid slice key"), st))))

theorem assSubRules_proven : AssSubRules := by
  intro st self key value hl
  dsimp only
  have e := checkReleased_ok st self hl
  refine ⟨fun er val hf => ?_, fun fmt hf => ⟨fun hr val => ?_, fun hr => ?_, fun hr h0 => ⟨?_, ?_, fun el => ?_⟩,
    fun hr h0 => ⟨?_, fun es h1 h2 => ?_, fun es h1 h2 => ?_, fun es h1 h2 => ?_, fun es h1 h2 => ?_⟩⟩⟩
  all_goals simp [memoryAssSub, M.bind_app, e, M.get, M.lift, *, M.throw_app, M.pure_app]

/-! ## Restricted views -/

/-- A restricted view reads like any other and makes no new reference to the buffer: `memoryview(m)`,
`m.cast`, `m.toreadonly()`, `m[a:b]` and `m.__buffer__` all raise
`ValueError("cannot create new view on restricted memoryview")` and change nothing, and `len(m)` works.
This is what stops a reference from outliving the buffer. Hypotheses: a live view, and, for the
slice, that it is not 0-dim, where the key is refused first. -/
def RestrictedRefuses : Prop :=
  ∀ (st : St) (i : Nat), baseInaccessible st i = false → (st.mv i).flags.restricted = true →
    let refused : PyExc := .valueError "cannot create new view on restricted memoryview"
    (∀ fl, memoryViewFromObjectAndFlags (.view i) fl st = (.error refused, st)) ∧
    (∀ f s, memoryviewCast i f s st = (.error refused, st)) ∧
    memoryviewToreadonly i st = (.error refused, st) ∧
    (∀ fl, memoryGetbuf i fl st = (.error refused, st)) ∧
    (∀ s r f, (st.mv i).view.ndim ≠ 0 → memorySubscript i (.one (.slice s r f)) st = (.error refused, st)) ∧
    ((st.mv i).view.ndim ≠ 0 → memoryLength i st = (.ok (((st.mv i).view.shape.getD []).getD 0 0), st))

theorem restrictedRefuses_proven : RestrictedRefuses := by
  intro st i hl hr
  dsimp only
  have e := checkReleased_ok st i hl
  have r : checkRestricted i st = (.error (.valueError "cannot create new view on restricted memoryview"), st) := by
    simp [checkRestricted, hr, restrictedError]
  refine ⟨fun fl => ?_, fun f s => ?_, ?_, fun fl => ?_, fun s rl f h => ?_, fun h => ?_⟩
  · simp [memoryViewFromObjectAndFlags, M.bind_app, e, r, M.get]
  · simp [memoryviewCast, M.bind_app, e, r]
  · simp [memoryviewToreadonly, M.bind_app, e, r]
  · simp [memoryGetbuf, M.bind_app, e, r]
  · simp [memorySubscript, M.bind_app, e, r, M.get, h]
  · simp [memoryLength, M.bind_app, e, M.get, h, M.pure_app]

/-- The only way a view becomes restricted: `releasebuffer_call_python` makes a new view of the buffer
and sets the flag. The new view stays live, so `RestrictedRefuses` applies to it, and it is not
restricted before. Hypotheses: `PyMemoryView_FromBuffer` made a live view, the case. -/
def RestrictedMade : Prop :=
  ∀ (b : Buf) (st s : St) (i : Nat), memoryViewFromBuffer b false st = (.ok i, s) → i < s.mvs.length →
    baseInaccessible s i = false →
    (restrictedView b st).1 = .ok i ∧ ((restrictedView b st).2.mv i).flags.restricted = true ∧
    baseInaccessible (restrictedView b st).2 i = false

theorem restrictedMade_proven : RestrictedMade := by
  intro b st s i h hi hl
  have e : restrictedView b st =
      (.ok i, s.setMv i { s.mv i with flags := { (s.mv i).flags with restricted := true } }) := by
    simp only [restrictedView, M.bind_app, h, M.modify, M.pure_app]
  rw [e]
  have hm := St.mv_setMv s i { s.mv i with flags := { (s.mv i).flags with restricted := true } } hi
  refine ⟨rfl, ?_, ?_⟩
  · simp only [hm]
  · have hb : baseInaccessible s i = false := hl
    simp only [baseInaccessible, Bool.or_eq_false_iff] at hb ⊢
    simp only [hm]
    exact hb

/-! ## `init_flags` -/

/-- Every bit of `init_flags`: a view with suboffsets is `PIL` and neither C nor Fortran, whatever its
strides say; otherwise a 0-dim view is scalar, and from two dimensions up the C and Fortran bits are
the two tests of `PyBuffer_IsContiguous`. The strides `cast` and `init_fortran_strides_from_shape`
give set the bits they should: `FortranBit`. Nothing is released or restricted. -/
def InitFlagsBits : Prop :=
  ∀ v : Buf, let f := initFlags v
    f.released = false ∧ f.restricted = false ∧ f.pil = v.suboffsets.isSome ∧
    (v.suboffsets.isSome = true → f.c = false ∧ f.fortran = false) ∧
    (v.suboffsets = none → 2 ≤ v.ndim → f.scalar = false ∧
      f.c = isCContiguous v ∧ f.fortran = isFortranContiguous v)

theorem initFlagsBits_proven : InitFlagsBits := by
  intro v
  dsimp only
  unfold initFlags
  dsimp only
  cases hs : v.suboffsets with
  | some s =>
    rcases hn : v.ndim with _ | _ | n
    · simp
    · by_cases hc : mvContiguousNdim1 v = true <;> simp [hc]
    · simp
  | none =>
    rcases hn : v.ndim with _ | _ | n
    · simp
    · by_cases hc : mvContiguousNdim1 v = true <;> simp [hc]
    · simp [pyBufferIsContiguous, hs]

/-- A view with no suboffsets whose strides are the Fortran strides of its shape has the Fortran bit
that `f_contiguous` reads. -/
def FortranBit : Prop :=
  ∀ (v : Buf) (sh : List Int), v.suboffsets = none → 2 ≤ v.ndim → v.shape = some sh →
    v.strides = some (fStrides v.itemsize sh) → (initFlags v).fortran = true

theorem fLoop_own : ∀ (sh : List Int) (sd : Int), fLoop sh (fStrides sd sh) sd = true
  | [], _ => rfl
  | d :: ds, sd => by
    simp only [fStrides, fLoop, ne_eq, not_true_eq_false, and_false, ↓reduceIte]
    exact fLoop_own ds (sd * d)

theorem fortranBit_proven : FortranBit := by
  intro v sh h1 h2 h3 h4
  have := (initFlagsBits_proven v).2.2.2.2 h1 h2
  rw [this.2.2]
  unfold isFortranContiguous
  split
  · rfl
  · simp only [h4, h3, Option.getD_some]
    exact fLoop_own sh v.itemsize

/-- With the flags `init_flags` gave it, a view from two dimensions up reports its contiguity through
the getters: `c_contiguous`, `f_contiguous` and `contiguous` are the tests of
`PyBuffer_IsContiguous`. Hypotheses: a live view, its flags as `init_flags` set them (a type
invariant), no suboffsets. -/
def ContigGetters : Prop :=
  ∀ (st : St) (i : Nat), baseInaccessible st i = false →
    let v := (st.mv i).view
    (st.mv i).flags = { initFlags v with released := (st.mv i).flags.released } →
    v.suboffsets = none → 2 ≤ v.ndim →
    (memoryGet i .cContiguous st).1 = .ok (.bool (isCContiguous v)) ∧
    (memoryGet i .fContiguous st).1 = .ok (.bool (isFortranContiguous v)) ∧
    (memoryGet i .contiguous st).1 = .ok (.bool (isCContiguous v || isFortranContiguous v))

theorem contigGetters_proven : ContigGetters := by
  intro st i hl
  dsimp only
  intro hf h1 h2
  obtain ⟨_, _, _, _, h3⟩ := initFlagsBits_proven (st.mv i).view
  obtain ⟨hs, hc, hF⟩ := h3 h1 h2
  have hr := gettersReport_proven st i hl
  dsimp only at hr
  obtain ⟨_, _, _, _, _, _, _, _, _, r1, r2, r3⟩ := hr
  rw [r1, r2, r3, hf]
  simp [hs, hc, hF]

/-- `_IntTupleFromSsizet`: NULL is the empty tuple, whatever the length, and otherwise the first
`len` values, in order. It is how `shape`, `strides` and `suboffsets` say "none". -/
def IntTupleSpec : Prop :=
  ∀ (n : Nat) (l : List Int),
    intTupleFromSsizet n none = [] ∧ (intTupleFromSsizet n (some l)).length = min n l.length ∧
    ∀ k, k < n → (intTupleFromSsizet n (some l))[k]? = l[k]?

theorem intTupleSpec_proven : IntTupleSpec := by
  intro n l
  simp only [intTupleFromSsizet]
  refine ⟨?_, ?_, fun k hk => ?_⟩
  · simp
  · simp
  · simp [List.getElem?_take, hk]

/-- `memory_clear` in a reference cycle: with no exports it is the release, so every later operation
is refused; with exports it does nothing. Hypothesis: a live object. -/
def ClearEffect : Prop :=
  ∀ (st : St) (i : Nat), i < st.mvs.length →
    ((st.mv i).exports = 0 → (memoryLength i (memoryClear i st).2).1 = .error releasedError) ∧
    ((st.mv i).exports ≠ 0 → memoryClear i st = (.ok (), st))

theorem clearEffect_proven : ClearEffect := by
  intro st i hi
  constructor
  · intro h
    have e : memoryClear i st = memoryRelease i st := by simp [memoryClear, getExports, h]
    rw [e]
    have hin := memoryRelease_inaccessible i st hi
    simp only [memoryLength, M.bind_app, checkReleased_err _ _ hin]
  · intro h
    simp [memoryClear, getExports, h]

/-- `memory_repr` has two texts, and which one depends on the view's own flag: after `release` it is
the released text, and before it the other, even when the managed buffer is gone. The address is out
of scope, since it is printed only. -/
def ReprStates : Prop :=
  ∀ (st : St) (i : Nat), i < st.mvs.length →
    ((st.mv i).flags.released = false → (memoryRepr i st).1 = .ok "<memory") ∧
    ((memoryRepr i (memoryRelease i st).2).1 = .ok "<released memory")

theorem reprStates_proven : ReprStates := by
  intro st i hi
  refine ⟨fun h => by simp [memoryRepr, h], ?_⟩
  simp [memoryRepr, memoryRelease_released i st hi]

/-! ## `pack_single`, by message -/

/-- The two errors of the integer formats, literally, through `pack_single`: an item with no
`__index__` is `TypeError`, and a value outside the format is `ValueError`, each naming the format.
Hypothesis: a live view. -/
def PackMessages : Prop :=
  ∀ (st : St) (self : Nat) (ptr : Int) (s : List Char), baseInaccessible st self = false →
    (packSingle self ptr (.str s) ['B'] st).1 =
      .error (.typeError "memoryview: invalid type for format 'B'") ∧
    (packSingle self ptr (.int 256) ['B'] st).1 =
      .error (.valueError "memoryview: invalid value for format 'B'") ∧
    (packSingle self ptr (.int (-1)) ['B'] st).1 =
      .error (.valueError "memoryview: invalid value for format 'B'") ∧
    (packSingle self ptr (.int 128) ['b'] st).1 =
      .error (.valueError "memoryview: invalid value for format 'b'") ∧
    (packSingle self ptr (.str s) ['q'] st).1 =
      .error (.typeError "memoryview: invalid type for format 'q'") ∧
    (packSingle self ptr (.int (2 ^ 63)) ['q'] st).1 =
      .error (.valueError "memoryview: invalid value for format 'q'")

theorem packMessages_proven : PackMessages := by
  intro st self ptr s hl
  have h1 := pack_int_err st self ptr 256 0 255 'B' 1 rfl hl (by omega)
  have h2 := pack_int_err st self ptr (-1) 0 255 'B' 1 rfl hl (by omega)
  have h3 := pack_int_err st self ptr 128 (-128) 127 'b' 1 rfl hl (by omega)
  have h4 := pack_int_err st self ptr (2 ^ 63) (-9223372036854775808) 9223372036854775807 'q' 8 rfl hl
    (by omega)
  have t1 : packSingle self ptr (.str s) ['B'] st = (.error (typeErrorInt ['B']), st) := by
    simp [packSingle, cc, M.bind_app, M.mapErr, pylongAsLu, numberIndex, M.throw_app]
  have t2 : packSingle self ptr (.str s) ['q'] st = (.error (typeErrorInt ['q']), st) := by
    simp [packSingle, cc, M.bind_app, M.mapErr, pylongAsLld, numberIndex, M.throw_app]
  rw [t1, t2, h1, h2, h3, h4]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Getters -/

/-- Every getter of a released view raises `ValueError("operation forbidden on released memoryview
object")` and changes nothing, which is the one branch these functions have. -/
def GetterRefusal : Prop :=
  ∀ (st : St) (i : Nat) (a : Attr), baseInaccessible st i = true →
    memoryGet i a st = (.error (.valueError "operation forbidden on released memoryview object"), st)

theorem getterRefusal_proven : GetterRefusal := by
  intro st i a h
  have e := checkReleased_err st i h
  simp only [memoryGet, M.bind_app, e]
  rfl

/-! ## `prepare_s` -/

/-- A repeat count past `PY_SSIZE_T_MAX`, or one whose item size takes the struct past it, is
`struct.error("total struct size too long")` however the format goes on, and for `==` that means
"not equal" (`fix_struct_error_int`). Hypotheses: the format starts with the count, native mode. -/
def StructSizeTooLong : Prop :=
  ∀ (d : Char) (ds : List Char) (c : Char) (rest : List Char),
    isDigit d = true → (∀ x ∈ ds, isDigit x = true) → isDigit c = false →
    let num := (spanDigits (d :: ds) 0).1
    ((num : Int) > ssizeMax →
      structParse (d :: ds ++ c :: rest) = .error sizeTooLong) ∧
    (∀ z, nativeSize c = some z → (num : Int) ≤ ssizeMax → (num : Int) > Int.tdiv ssizeMax z →
      structParse (d :: ds ++ c :: rest) = .error sizeTooLong) ∧
    fixStructError sizeTooLong = .ok false

theorem digit_not_prefix (d : Char) (h : isDigit d = true) :
    d ≠ '<' ∧ d ≠ '>' ∧ d ≠ '!' ∧ d ≠ '=' ∧ d ≠ '@' ∧ isCSpace d = false := by
  have h2 : 48 ≤ d.toNat ∧ d.toNat ≤ 57 := by simpa [isDigit] using h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro rfl; simp at h2
  · rintro rfl; simp at h2
  · rintro rfl; simp at h2
  · rintro rfl; simp at h2
  · rintro rfl; simp at h2
  · simp only [isCSpace, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, Bool.and_eq_false_iff,
      decide_eq_false_iff_not]
    constructor
    · rintro rfl
      simp at h2
    · right
      omega

theorem structSizeTooLong_proven : StructSizeTooLong := by
  intro d ds c rest hd hds hc
  dsimp only
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := digit_not_prefix d hd
  have hsp : spanDigits (d :: ds ++ c :: rest) 0 = ((spanDigits (d :: ds) 0).1, c :: rest) :=
    spanDigits_app c rest hc (d :: ds) 0 (by
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hd
      · exact hds x hx)
  generalize (spanDigits (d :: ds) 0).1 = num at hsp
  have hmain : structParse (d :: ds ++ c :: rest) =
      (match parseCodes true ((d :: ds ++ c :: rest).length + 1) (d :: ds ++ c :: rest) 0 [] with
       | .ok (codes, size) => .ok ⟨false, codes, size⟩
       | .error e => .error e) := by
    simp [structParse, n1, n2, n3, n4, n5]
    rfl
  simp only [List.cons_append, List.length_cons] at hsp hmain
  refine ⟨fun h => ?_, fun z hz h1 h2 => ?_, ?_⟩
  · simp only [List.cons_append]
    rw [hmain]
    simp only [parseCodes, n6, Bool.false_eq_true, ↓reduceIte, hd, hsp, h]
  · simp only [List.cons_append]
    rw [hmain]
    have h3 : ¬ ((num : Int) > ssizeMax) := by omega
    have hcZ : c ≠ 'Z' := by
      rintro rfl
      simp [nativeSize] at hz
    have he : entryAt true c rest = some (c, z, z, rest) := by simp [entryAt, hcZ, hz]
    have h4 : alignTo 0 z = 0 := by simp [alignTo]
    have h5 : ¬ (((0 : Nat) : Int) > ssizeMax) := by unfold ssizeMax; omega
    have h6 : (num : Int) > Int.tdiv (ssizeMax - ((0 : Nat) : Int)) z := by simpa using h2
    simp only [parseCodes, n6, Bool.false_eq_true, ↓reduceIte, hd, hsp, h3, he, h4, h5, h6]
  · simp [fixStructError, sizeTooLong, structError, excMatches, PyExc.className, excBases]

/-- An item too large to allocate is `MemoryError`, after the format is accepted, and
`fix_struct_error_int` lets it out of `==`, where a bad format would be "not equal". -/
def StructNoMemory : Prop :=
  ∀ (fmt : List Char) (sf : SFmt) (n : Int), structParse fmt = .ok sf → n ≥ 2 ^ 47 →
    structGetUnpacker fmt n = .error noMemory ∧ fixStructError noMemory = .error noMemory

theorem structNoMemory_proven : StructNoMemory := by
  intro fmt sf n h hn
  constructor
  · simp only [structGetUnpacker, h, bind, Except.bind]
    rw [if_pos hn]
    rfl
  · simp [fixStructError, noMemory, excMatches, PyExc.className]

/-! ## `NULL` -/

/-- What `memoryiter_next` tests for is reachable: a stored pointer of 0 with a suboffset of 0 is
`NULL`, and a positive suboffset never is. `IterNull` is what happens then. -/
def NullReachable : Prop :=
  ∀ (m : Mem) (p s : Int), rdU m p 8 = 0 →
    adjustPtr m p (some [0]) 0 = nullPtr ∧ (0 < s → adjustPtr m p (some [s]) 0 ≠ nullPtr)

theorem nullReachable_proven : NullReachable := by
  intro m p s h
  constructor
  · simp [adjustPtr, h, nullPtr]
  · intro hs
    have : ¬ s < 0 := by omega
    simp [adjustPtr, h, nullPtr, this]
    omega

/-! ## Equality and truth -/

/-- `item == value` for a memoryview `value`. An `int`, `float` or `bool` item never equals one, and
neither does anything equal a released view; a `bytes` item, the items of format `c`, gets
`NotImplemented` from `bytes_richcompare` and the reflected `memory_richcompare` decides: against a
view of format `B`, the one byte of the item equals the view exactly when the view holds that one
byte. This is why `memoryview(b'a').cast('c').count(memoryview(b'a'))` is 1. Hypotheses: for the last
two, a live 1-D view of format `B` with no suboffsets. -/
def ItemEqView : Prop :=
  (∀ (st : St) (i : Item) (j : Nat), (∀ b, i ≠ .bytes b) → itemEqM i (.view j) st = (.ok false, st)) ∧
  (∀ (st : St) (b : List Nat) (j : Nat), baseInaccessible st j = true →
    (itemEqM (.bytes b) (.view j) st).1 = .ok false) ∧
  (∀ (st : St) (c : Nat) (j : Nat) (d : Int), baseInaccessible st j = false →
    let v := (st.mv j).view
    v.format = some ['B'] → v.ndim = 1 → v.shape = some [1] → v.strides = some [d] → v.suboffsets = none →
    0 ≤ v.buf → v.buf < st.mem.length →
    (itemEqM (.bytes [c]) (.view j) st).1 = .ok (rdByte st.mem v.buf == c)) ∧
  (∀ (st : St) (c : Nat) (j : Nat) (n d : Int), baseInaccessible st j = false →
    let v := (st.mv j).view
    v.format = some ['B'] → v.ndim = 1 → v.shape = some [n] → v.strides = some [d] → n ≠ 1 →
    (itemEqM (.bytes [c]) (.view j) st).1 = .ok false)

/-- The buffer of a `bytes` object placed at `a`. -/
def bytesView (a : Int) (b : List Nat) : Buf :=
  { obj := some (.exp 1000000), buf := a, len := b.length, itemsize := 1, readonly := true,
    ndim := 1, format := some ['B'], shape := some [b.length], strides := some [1] }

theorem bytesBuf_eq (b : List Nat) (st : St) :
    bytesBuf b st = (.ok (bytesView st.mem.length b), { st with mem := st.mem ++ b }) := rfl

theorem rich_bytes (st : St) (j : Nat) (b : List Nat) (hl : baseInaccessible st j = false) :
    (memoryRichEqual j (.bytes b) st).1 =
      some <$> compareBufs (st.mem ++ b) st.noStruct (st.mv j).view (bytesView st.mem.length b) := by
  have tc : (tryCatch (some <$> getBufferFull (.bytes b))
      (fun _ => pure Option.none) : M (Option Buf)) st =
        (.ok (some (bytesView st.mem.length b)), { st with mem := st.mem ++ b }) := by
    have hm : (some <$> getBufferFull (.bytes b) : M (Option Buf)) st =
        (.ok (some (bytesView st.mem.length b)), { st with mem := st.mem ++ b }) := by
      have gb : getBufferFull (.bytes b) st =
          (.ok (bytesView st.mem.length b), { st with mem := st.mem ++ b }) := rfl
      show (getBufferFull (.bytes b) >>= fun a => pure (some a)) st = _
      rw [M.bind_app, gb]
      rfl
    simp [tryCatch, MonadExcept.tryCatch, hm]
  have hq : ((Obj.bytes b == Obj.view j) && selfEqualFormat (st.mv j).view.format) = false := by simp
  simp only [memoryRichEqual, M.bind_app, M.get, hl, Bool.false_eq_true, ↓reduceIte, hq, tc]
  rcases hr : pyBufferRelease (bytesView st.mem.length b) { st with mem := st.mem ++ b } with ⟨r0, s⟩
  have hok := pyBufferRelease_ok (bytesView st.mem.length b) { st with mem := st.mem ++ b }
  rw [hr] at hok
  simp only at hok
  subst hok
  simp only [M.lift, M.pure_app]
  cases compareBufs (st.mem ++ b) st.noStruct (st.mv j).view (bytesView st.mem.length b) <;> rfl

theorem itemEq_bytes_view (st : St) (j : Nat) (b : List Nat) :
    (itemEqM (.bytes b) (.view j) st).1 =
      (fun r => r.getD false) <$> (memoryRichEqual j (.bytes b) st).1 := by
  simp only [itemEqM, M.bind_app]
  rcases memoryRichEqual j (.bytes b) st with ⟨r, s⟩
  cases r <;> rfl

theorem itemEqView_proven : ItemEqView := by
  refine ⟨fun st i j h => ?_, fun st b j h => ?_, fun st c j d hl hf hn hs hd hu h0 hb => ?_,
    fun st c j n d hl hf hn hs hd hne => ?_⟩
  · cases i with
    | bytes b => exact absurd rfl (h b)
    | _ => rfl
  · rw [itemEq_bytes_view]
    simp [memoryRichEqual, M.bind_app, M.get, h, M.pure_app]
    rfl
  · have hfm : getNativeFmtchar ['B'] = some ('B', 1) := by decide
    have hrd : rdByte (st.mem ++ [c]) (st.mv j).view.buf = rdByte st.mem (st.mv j).view.buf := by
      simp only [rdByte, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    have hrd2 : rdByte (st.mem ++ [c]) (st.mem.length : Int) = c := by
      simp [rdByte, List.getD_eq_getElem?_getD]
    rw [itemEq_bytes_view, rich_bytes st j _ hl]
    simp [compareBufs, equivShape, shapeLoop, bytesView, hf, hn, hs, hd, hu, hfm, cmpBase, unpackCmp,
      unpackCmpNative, adjustPtr, hrd, hrd2, bind, Except.bind, pure, Except.pure]
    by_cases hh : rdByte st.mem (st.mv j).view.buf = c <;> simp [hh]
  · rw [itemEq_bytes_view, rich_bytes st j _ hl]
    have he : equivShape (st.mv j).view (bytesView st.mem.length [c]) = false := by
      simp [equivShape, shapeLoop, bytesView, hn, hs, hne]
    simp [compareBufs, he]

/-- What `__eq__` returned is only tested for truth, so a `str` result counts and `None` does not.
`m.count(x)` for a value whose `__eq__` returns a true object is the length, for a false one 0. -/
def EqTruth : Prop :=
  ∀ (st : St) (i : Item),
    itemEqM i (.eqLike (.wrong "str") none) st = (.ok true, st) ∧
    itemEqM i (.eqLike (.wrong "NoneType") none) st = (.ok false, st) ∧
    itemEqM i (.eqLike (.wrong "list") none) st = (.ok false, st) ∧
    ∀ b, itemEqM i (.eqLike (.val b) none) st = (.ok b, st)

theorem eqTruth_proven : EqTruth := by
  intro st i
  refine ⟨rfl, rfl, rfl, fun b => rfl⟩

/-- Storing through `?` an object with `__len__` and no `__bool__`: `PyObject_IsTrue` calls it, so 0
stores 0 and a positive length stores 1; a negative one and an exception raise, write nothing, and
keep their class (the `preserve original error` of @3.14.7:1988-1989). Hypotheses: a live view, and the
item's byte is in the store. -/
def PackBoolLen : Prop :=
  ∀ (st : St) (self : Nat) (ptr : Int) (n : Int) (e : PyExc), baseInaccessible st self = false →
    0 ≤ ptr → ptr + 8 ≤ st.mem.length →
    (0 ≤ n → ∃ s, packSingle self ptr (.lenLike (.val n) none) ['?'] st = (.ok (), s) ∧
      unpackRaw s.mem ptr ['?'] = .ok (.bool (n != 0))) ∧
    (n < 0 → packSingle self ptr (.lenLike (.val n) none) ['?'] st =
      (.error (.valueError "__len__() should return >= 0"), st)) ∧
    packSingle self ptr (.lenLike (.raises e) none) ['?'] st = (.error e, st) ∧
    packSingle self ptr (.lenLike (.wrong "str") none) ['?'] st =
      (.error (.typeError "'str' object cannot be interpreted as an integer"), st)

theorem packBoolLen_proven : PackBoolLen := by
  intro st self ptr n e hl h0 h8
  have hu := (packUnpackOther_proven st self ptr h0 h8).2 hl
  refine ⟨fun hn => ?_, fun hn => ?_, ?_, ?_⟩
  · have hi : isTrue (.lenLike (.val n) none) st = (.ok (n != 0), st) := by
      simp [isTrue, fire, M.bind_app, Ret.get, M.pure_app, show ¬ n < 0 by omega]
    exact hu.1 _ _ hi
  · simp [packSingle, cc, isTrue, fire, M.bind_app, Ret.get, M.pure_app, hn, M.throw_app]
  · have h : isTrue (.lenLike (.raises e) none) st = (.error e, st) := rfl
    simp only [packSingle, cc, List.getD_cons_zero, M.bind_app, h]
  · have h : isTrue (.lenLike (.wrong "str") none) st =
        (.error (.typeError "'str' object cannot be interpreted as an integer"), st) := rfl
    simp only [packSingle, cc, List.getD_cons_zero, M.bind_app, h]

end PyLean.BytesObj.Mem
