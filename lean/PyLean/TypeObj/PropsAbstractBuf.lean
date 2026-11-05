import PyLean.TypeObj.PropsBuffer

/-!
Exact truth conditions for the buffer helpers of `Objects/abstract.c`: `_IsCContiguous`,
`_IsFortranContiguous`, `PyBuffer_IsContiguous`, and the index odometers
`_Py_add_one_to_index_F` / `_C`.

Each contiguity test is characterised by an "if and only if" against the closed form of the
contiguous strides, so a test that always answers `true`, or always `false`, contradicts it.
The odometers are characterised as adding one in mixed radix modulo the number of elements,
which together with `AddOneInRange` determines every digit.

The hypotheses are the `Py_buffer` invariants of the buffer protocol documentation: `shape` and
`strides` have `ndim` entries, and index digits lie in `[0, shape[i])`.
-/

namespace PyLean.TypeObj

/-- The product of a list. -/
def prodL : List Int → Int
  | [] => 1
  | x :: xs => x * prodL xs

theorem prodL_append (a b : List Int) : prodL (a ++ b) = prodL a * prodL b := by
  induction a with
  | nil => simp [prodL]
  | cons x xs ih => simp [prodL, ih, Int.mul_assoc]

theorem prodL_reverse (a : List Int) : prodL a.reverse = prodL a := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    simp [prodL_append, ih, prodL, Int.mul_comm]

/-! ## Contiguity -/

/-- The stride walk over an appended list: the first part, then the rest from the product of
the first part's dimensions. -/
theorem stridesMatch_append (sd : Int) (a b : List (Int × Int)) :
    stridesMatch sd (a ++ b) =
      (stridesMatch sd a && stridesMatch (sd * prodL (a.map Prod.fst)) b) := by
  induction a generalizing sd with
  | nil => simp [stridesMatch, prodL]
  | cons p a ih =>
    obtain ⟨d, s⟩ := p
    simp only [List.cons_append, stridesMatch, List.map_cons, prodL]
    by_cases h : (decide (d > 1) && s != sd) = true
    · simp [h]
    · simp only [h, Bool.false_eq_true, ite_false]
      rw [ih]
      simp [Int.mul_assoc]

/-- Fortran order: the walk accepts exactly when every dimension longer than 1 has the stride
`sd * shape[0] * ... * shape[i-1]`. -/
theorem stridesMatch_F_iff (sd : Int) (shape st : List Int) (h : st.length = shape.length) :
    stridesMatch sd (shape.zip st) = true ↔
      ∀ i < shape.length, 1 < shape.getD i 0 → st.getD i 0 = sd * prodL (shape.take i) := by
  induction shape generalizing sd st with
  | nil => simp [stridesMatch]
  | cons d ds ih =>
    cases st with
    | nil => simp at h
    | cons s ss =>
      have hl : ss.length = ds.length := by simpa using h
      simp only [List.zip_cons_cons, stridesMatch]
      rw [show (if (decide (d > 1) && s != sd) = true then false
              else stridesMatch (sd * d) (ds.zip ss)) = true ↔
            ((1 < d → s = sd) ∧ stridesMatch (sd * d) (ds.zip ss) = true) by
        by_cases hd : 1 < d <;> by_cases hs : s = sd <;> simp [hd, hs]]
      rw [ih (sd * d) ss hl]
      constructor
      · rintro ⟨h0, hr⟩ i hi hgt
        cases i with
        | zero => simpa [prodL] using h0 (by simpa using hgt)
        | succ i =>
          have := hr i (by simpa using hi) (by simpa using hgt)
          simp only [List.getD_cons_succ, List.take_succ_cons, prodL]
          rw [this, Int.mul_assoc]
      · intro hall
        refine ⟨fun hd => ?_, fun i hi hgt => ?_⟩
        · simpa [prodL] using hall 0 (by simp) (by simpa using hd)
        · have := hall (i + 1) (by simp; omega) (by simpa using hgt)
          simpa [prodL, Int.mul_assoc] using this

/-- C order: the walk from the last dimension accepts exactly when every dimension longer than 1
has the stride `sd * shape[i+1] * ... * shape[ndim-1]`. -/
theorem stridesMatch_C_iff (sd : Int) (shape st : List Int) (h : st.length = shape.length) :
    stridesMatch sd (shape.zip st).reverse = true ↔
      ∀ i < shape.length, 1 < shape.getD i 0 → st.getD i 0 = sd * prodL (shape.drop (i + 1)) := by
  induction shape generalizing st with
  | nil => simp [stridesMatch]
  | cons d ds ih =>
    cases st with
    | nil => simp at h
    | cons s ss =>
      have hl : ss.length = ds.length := by simpa using h
      have hfst : ((ds.zip ss).reverse.map Prod.fst) = ds.reverse := by
        rw [List.map_reverse, List.map_fst_zip (by omega)]
      simp only [List.zip_cons_cons, List.reverse_cons, stridesMatch_append, hfst,
        prodL_reverse, Bool.and_eq_true]
      rw [ih ss hl]
      have h1 : stridesMatch (sd * prodL ds) [(d, s)] = true ↔ (1 < d → s = sd * prodL ds) := by
        by_cases hd : 1 < d <;> by_cases hs : s = sd * prodL ds <;> simp [stridesMatch, hd, hs]
      rw [h1]
      constructor
      · rintro ⟨hr, h0⟩ i hi hgt
        cases i with
        | zero => simpa using h0 (by simpa using hgt)
        | succ i => simpa using hr i (by simpa using hi) (by simpa using hgt)
      · intro hall
        refine ⟨fun i hi hgt => ?_, fun hd => ?_⟩
        · simpa using hall (i + 1) (by simp; omega) (by simpa using hgt)
        · simpa using hall 0 (by simp) (by simpa using hd)

/-- The `Py_buffer` invariant these functions rely on: `shape` and `strides` (when present) have
`ndim` entries. -/
def BufWellFormed (v : BufView) : Prop :=
  v.shape.length = v.ndim ∧ ∀ st, v.strides = some st → st.length = v.ndim

/-- **`_IsCContiguous` decides C contiguity exactly.** For a well-formed view, the test is true
if and only if the view is empty, has no strides (C-contiguous by definition), or every
dimension longer than 1 has the stride `itemsize * shape[i+1] * ... * shape[ndim-1]`.
`Objects/abstract.c:501-525`. -/
def CContiguousExact : Prop :=
  ∀ v : BufView, BufWellFormed v →
    (isCContiguous v = true ↔
      v.len = 0 ∨ v.strides = none ∨
      ∃ st, v.strides = some st ∧
        ∀ i < v.ndim, 1 < v.shape.getD i 0 →
          st.getD i 0 = v.itemsize * prodL (v.shape.drop (i + 1)))

theorem cContiguousExact_proven : CContiguousExact := by
  intro v ⟨hs, hst⟩
  unfold isCContiguous
  by_cases hl : v.len = 0
  · simp [hl]
  · simp only [hl, beq_iff_eq, ite_false, false_or]
    cases hv : v.strides with
    | none => simp
    | some st =>
      have hlen : st.length = v.shape.length := by rw [hst st hv, hs]
      simp only [Option.some.injEq, exists_eq_left', reduceCtorEq, false_or]
      rw [stridesMatch_C_iff _ _ _ hlen, hs]

/-- **`_IsFortranContiguous` decides Fortran contiguity exactly.** For a well-formed view, true
if and only if the view is empty; or it has no strides (so it is C-contiguous) and is
effectively one-dimensional, `ndim <= 1` or at most one dimension longer than 1; or every
dimension longer than 1 has the stride `itemsize * shape[0] * ... * shape[i-1]`.
`Objects/abstract.c:461-498`. -/
def FortranContiguousExact : Prop :=
  ∀ v : BufView, BufWellFormed v →
    (isFortranContiguous v = true ↔
      v.len = 0 ∨
      (v.strides = none ∧ (v.ndim ≤ 1 ∨ (v.shape.filter (1 < ·)).length ≤ 1)) ∨
      ∃ st, v.strides = some st ∧
        ∀ i < v.ndim, 1 < v.shape.getD i 0 → st.getD i 0 = v.itemsize * prodL (v.shape.take i))

theorem fortranContiguousExact_proven : FortranContiguousExact := by
  intro v ⟨hs, hst⟩
  unfold isFortranContiguous
  by_cases hl : v.len = 0
  · simp [hl]
  · simp only [hl, beq_iff_eq, ite_false, false_or]
    cases hv : v.strides with
    | none =>
      simp only [true_and, reduceCtorEq, false_and, exists_false, or_false]
      by_cases hn : v.ndim ≤ 1
      · simp [hn]
      · simp [hn]
    | some st =>
      have hlen : st.length = v.shape.length := by rw [hst st hv, hs]
      simp only [Option.some.injEq, exists_eq_left', reduceCtorEq, false_and, false_or]
      rw [stridesMatch_F_iff _ _ _ hlen, hs]

/-- **`PyBuffer_IsContiguous` dispatches exactly**: a view with suboffsets is never contiguous;
otherwise `'C'` asks `_IsCContiguous`, `'F'` asks `_IsFortranContiguous`, `'A'` asks either, and
any other order is refused. `Objects/abstract.c:528-540`. With `CContiguousExact` and
`FortranContiguousExact` this is the full truth condition. -/
def IsContiguousExact : Prop :=
  ∀ (v : BufView) (o : Char),
    isContiguous v o = true ↔
      v.hasSuboffsets = false ∧
      ((o = 'C' ∧ isCContiguous v = true) ∨ (o = 'F' ∧ isFortranContiguous v = true) ∨
        (o = 'A' ∧ (isCContiguous v = true ∨ isFortranContiguous v = true)))

theorem isContiguousExact_proven : IsContiguousExact := by
  intro v o
  unfold isContiguous
  cases hsub : v.hasSuboffsets <;> simp only [ite_true, Bool.false_eq_true, ite_false]
  · by_cases hC : o = 'C'
    · subst hC; simp
    · by_cases hF : o = 'F'
      · subst hF; simp
      · by_cases hA : o = 'A'
        · subst hA; simp
        · simp [hC, hF, hA]
  · simp

/-- A concrete pin of both tests: a 2x3 byte array with strides `(3, 1)` is C-contiguous and not
Fortran-contiguous, and with strides `(1, 2)` the other way round; strides `(6, 1)` are neither. -/
def ContiguousExamples : Prop :=
  isContiguous ⟨6, 1, 2, [2, 3], some [3, 1], false⟩ 'C' = true ∧
  isContiguous ⟨6, 1, 2, [2, 3], some [3, 1], false⟩ 'F' = false ∧
  isContiguous ⟨6, 1, 2, [2, 3], some [1, 2], false⟩ 'F' = true ∧
  isContiguous ⟨6, 1, 2, [2, 3], some [1, 2], false⟩ 'C' = false ∧
  isContiguous ⟨6, 1, 2, [2, 3], some [6, 1], false⟩ 'A' = false ∧
  isContiguous ⟨6, 1, 2, [2, 3], some [3, 1], true⟩ 'A' = false

theorem contiguousExamples_proven : ContiguousExamples := by unfold ContiguousExamples; decide

/-! ## The index odometers -/

/-- The mixed-radix value of a Fortran-order index: the first digit varies fastest. -/
def odoValF : List Int → List Int → Int
  | i :: is, s :: ss => i + s * odoValF is ss
  | _, _ => 0

/-- The value of a C-order index: the last digit varies fastest. -/
def odoValC (index shape : List Int) : Int := odoValF index.reverse shape.reverse

theorem inRange_bounds : ∀ (index shape : List Int), InRange index shape →
    0 ≤ odoValF index shape ∧ odoValF index shape < prodL shape ∧ 0 < prodL shape
  | [], [], _ => by simp [odoValF, prodL]
  | [], _ :: _, h => by simp [InRange] at h
  | _ :: _, [], h => by simp [InRange] at h
  | i :: is, s :: ss, h => by
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨b1, b2, b3⟩ := inRange_bounds is ss h3
    simp only [odoValF, prodL]
    have hs : 0 < s := by omega
    refine ⟨?_, ?_, Int.mul_pos hs b3⟩
    · exact Int.add_nonneg h1 (Int.mul_nonneg (by omega) b1)
    · -- i + s * v ≤ (s - 1) + s * (P - 1) = s * P - 1
      have : s * odoValF is ss ≤ s * (prodL ss - 1) :=
        Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      rw [Int.mul_sub, Int.mul_one] at this
      omega

theorem inRange_length : ∀ (index shape : List Int), InRange index shape →
    index.length = shape.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [InRange] at h
  | _ :: _, [], h => by simp [InRange] at h
  | _ :: is, _ :: ss, h => by simp [inRange_length is ss h.2.2]

theorem inRange_append : ∀ (a b c d : List Int), a.length = b.length →
    (InRange (a ++ c) (b ++ d) ↔ InRange a b ∧ InRange c d)
  | [], [], c, d, _ => by simp [InRange]
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | i :: is, s :: ss, c, d, h => by
    have hl : is.length = ss.length := by simpa using h
    simp [InRange, inRange_append is ss c d hl, and_assoc]

theorem inRange_reverse (a b : List Int) (h : InRange a b) : InRange a.reverse b.reverse := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simp [InRange]
    | cons _ _ => simp [InRange] at h
  | cons i is ih =>
    cases b with
    | nil => simp [InRange] at h
    | cons s ss =>
      obtain ⟨h1, h2, h3⟩ := h
      simp only [List.reverse_cons]
      have hl : is.reverse.length = ss.reverse.length := by
        simp [inRange_length is ss h3]
      rw [inRange_append _ _ _ _ hl]
      exact ⟨ih ss h3, by simp [InRange]; omega⟩

/-- **`_Py_add_one_to_index_F` adds one in mixed radix.** For an index within the shape, the
result is again within the shape, and its Fortran-order value (first digit fastest) is the old
value plus one, wrapping to zero after the last element. The increment of the first digit below
its bound, the zeroing of the digits before it, and the wrap are all pinned: a mixed-radix
representation within the shape is unique. `Objects/abstract.c:560-573`. -/
def AddOneFExact : Prop :=
  ∀ (index shape : List Int), InRange index shape →
    InRange (addOneF index shape) shape ∧
    odoValF (addOneF index shape) shape = (odoValF index shape + 1) % prodL shape

theorem addOneF_val : ∀ (index shape : List Int), InRange index shape →
    odoValF (addOneF index shape) shape = (odoValF index shape + 1) % prodL shape
  | [], [], _ => by simp [addOneF, odoValF, prodL]
  | [], _ :: _, h => by simp [InRange] at h
  | _ :: _, [], h => by simp [InRange] at h
  | i :: is, s :: ss, h => by
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨b1, b2, b3⟩ := inRange_bounds is ss h3
    have hs : 0 < s := by omega
    have hle : s * odoValF is ss ≤ s * (prodL ss - 1) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    rw [Int.mul_sub, Int.mul_one] at hle
    simp only [addOneF, prodL]
    split
    · -- the first digit can still grow
      simp only [odoValF]
      rw [Int.emod_eq_of_lt (by have := Int.mul_nonneg (Int.le_of_lt hs) b1; omega) (by omega)]
      omega
    · -- the first digit is maximal: it becomes 0 and the carry goes on
      have hi : i = s - 1 := by omega
      simp only [odoValF, Int.zero_add]
      rw [addOneF_val is ss h3]
      have hv : i + s * odoValF is ss + 1 = s * (odoValF is ss + 1) := by
        rw [hi, Int.mul_add, Int.mul_one]; omega
      rw [hv]
      by_cases hlt : odoValF is ss + 1 < prodL ss
      · rw [Int.emod_eq_of_lt (by omega) hlt]
        rw [Int.emod_eq_of_lt (Int.mul_nonneg (by omega) (by omega))
          (Int.mul_lt_mul_of_pos_left hlt hs)]
      · have heq : odoValF is ss + 1 = prodL ss := by omega
        rw [heq, Int.emod_self, Int.emod_self, Int.mul_zero]

theorem addOneFExact_proven : AddOneFExact :=
  fun index shape h => ⟨addOneInRange_proven index shape h, addOneF_val index shape h⟩

/-- **`_Py_add_one_to_index_C` adds one in mixed radix, last digit fastest**: the C-order twin of
`AddOneFExact`, with the walk running from `nd - 1` down to `0`.
`Objects/abstract.c:576-589`. -/
def AddOneCExact : Prop :=
  ∀ (index shape : List Int), InRange index shape →
    InRange (addOneC index shape) shape ∧
    odoValC (addOneC index shape) shape = (odoValC index shape + 1) % prodL shape

theorem addOneCExact_proven : AddOneCExact := by
  intro index shape h
  have hr := inRange_reverse _ _ h
  have h1 := addOneInRange_proven _ _ hr
  refine ⟨?_, ?_⟩
  · have := inRange_reverse _ _ h1
    simpa [addOneC] using this
  · simp only [odoValC, addOneC, List.reverse_reverse]
    rw [addOneF_val _ _ hr, prodL_reverse]

/-- A concrete pin: in shape `(2, 3)` the Fortran odometer goes `(1, 0) → (0, 1)` and the C
odometer goes `(0, 2) → (1, 0)`, and both wrap from the last index to `(0, 0)`. -/
def AddOneExamples : Prop :=
  addOneF [1, 0] [2, 3] = [0, 1] ∧ addOneF [0, 1] [2, 3] = [1, 1] ∧
  addOneF [1, 2] [2, 3] = [0, 0] ∧
  addOneC [0, 2] [2, 3] = [1, 0] ∧ addOneC [0, 0] [2, 3] = [0, 1] ∧
  addOneC [1, 2] [2, 3] = [0, 0]

theorem addOneExamples_proven : AddOneExamples := by unfold AddOneExamples; decide

end PyLean.TypeObj
