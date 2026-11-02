import PyLean.BytesObj.Bytes.BasicProps5
import PyLean.Sequences.SliceAssign

/-!
Properties of `bytearray`.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch
open PyLean.RangeSlice (Slice)

/-! ## resize -/

theorem resizedData_length (d : List Int) (n : Int) (h0 : 0 ≤ n) :
    ((resizedData d n).length : Int) = n := by
  simp only [resizedData, List.length_append, List.length_take, List.length_replicate]
  omega

/-- The buffer layout survives a resize: for every object with a valid layout and every
request, a successful `bytearray_resize_lock_held` gives the requested size and a valid layout
(the data inside the bytes object), keeps the first `min(old, new)` bytes, and
leaves the export count alone. This is what makes every `memcpy` after a resize safe. -/
def ResizeWF : Prop :=
  ∀ (b r : BA) (n : Int), b.WF → baResize b n = .ok r →
    r.WF ∧ r.size = n ∧ r.exports = b.exports ∧
    r.data.take b.data.length = b.data.take n.toNat

theorem baNewAlloc_ge (alloc offset n a : Int) (h0 : 0 ≤ n) (h : baNewAlloc alloc offset n = some a) :
    n ≤ a := by
  unfold baNewAlloc at h
  have : 0 ≤ n / 8 := Int.ediv_nonneg h0 (by decide)
  repeat' split at h
  all_goals simp only [Option.some.injEq, reduceCtorEq] at h
  all_goals (try subst h)
  all_goals omega

theorem baNewAlloc_le (alloc offset n a : Int) (h0 : 0 ≤ n) (h : baNewAlloc alloc offset n = some a) :
    a ≤ n + n / 8 + 6 := by
  unfold baNewAlloc at h
  have : 0 ≤ n / 8 := Int.ediv_nonneg h0 (by decide)
  repeat' split at h
  all_goals simp only [Option.some.injEq, reduceCtorEq] at h
  all_goals (try subst h)
  all_goals omega

theorem baNewAlloc_none (alloc offset n : Int) (h : baNewAlloc alloc offset n = none) :
    n + offset ≤ alloc := by
  unfold baNewAlloc at h
  repeat' split at h
  all_goals simp_all

theorem baResizeAlloc_cases (b : BA) (n a o : Int) (h0 : 0 ≤ n) (h : baResizeAlloc b n = .ok (a, o)) :
    (n + b.offset ≤ b.alloc ∧ a = b.alloc ∧ o = b.offset) ∨ (o = 0 ∧ n ≤ a) := by
  unfold baResizeAlloc at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    right
    omega
  · split at h
    · rename_i hn
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact Or.inl ⟨baNewAlloc_none _ _ _ hn, h.1.symm, h.2.symm⟩
    · rename_i x hn
      split at h
      · simp at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        have := baNewAlloc_ge _ _ _ _ h0 hn
        right
        omega

theorem baResize_cases (b r : BA) (n : Int) (h : baResize b n = .ok r) :
    0 ≤ n ∧ (r = b ∧ n = b.size ∨ b.exports = 0 ∧ n ≠ b.size ∧ r.data = resizedData b.data n ∧
      r.exports = b.exports ∧
      ((n + b.offset ≤ b.alloc ∧ r.alloc = b.alloc ∧ r.offset = b.offset) ∨
       (r.offset = 0 ∧ n ≤ r.alloc))) := by
  unfold baResize at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  by_cases h0 : n < 0
  · simp [h0] at h
  rw [if_neg h0] at h
  have h0' : 0 ≤ n := by omega
  refine ⟨h0', ?_⟩
  by_cases hne : n = b.size
  · rw [if_pos hne] at h
    simp only [Except.ok.injEq] at h
    exact Or.inl ⟨h.symm, hne⟩
  rw [if_neg hne] at h
  right
  by_cases hx : b.exports > 0
  · simp [canResize, hx] at h
  have hE : b.exports = 0 := by omega
  have hc : canResize b = .ok () := by simp [canResize, hE]
  rw [hc] at h
  simp only at h
  cases hA : baResizeAlloc b n with
  | error e => rw [hA] at h; simp at h
  | ok p =>
    rw [hA] at h
    obtain ⟨a, o⟩ := p
    simp only [Except.ok.injEq] at h
    subst h
    have := baResizeAlloc_cases b n a o h0' hA
    exact ⟨hE, hne, rfl, rfl, this⟩

theorem resizeWF_proven : ResizeWF := by
  intro b r n hw h
  obtain ⟨h0, hc⟩ := baResize_cases b r n h
  rcases hc with ⟨rfl, hn⟩ | ⟨hE, hne, hd, hx, hc⟩
  · refine ⟨hw, hn.symm, rfl, ?_⟩
    have : n.toNat = r.data.length := by simp [BA.size] at hn; omega
    simp [this]
  · have hsize : r.size = n := by
      simp only [BA.size, hd]
      exact resizedData_length _ _ h0
    refine ⟨?_, hsize, hx, ?_⟩
    · rcases hc with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
      · refine ⟨by rw [h3]; exact hw.1, ?_⟩
        omega
      · exact ⟨by omega, by omega⟩
    · rw [hd]
      simp only [resizedData]
      by_cases hle : n.toNat ≤ b.data.length
      · have e : n.toNat - b.data.length = 0 := by omega
        simp only [e, List.replicate_zero, List.append_nil]
        exact List.take_of_length_le (by simp; omega)
      · have e : b.data.take n.toNat = b.data := List.take_of_length_le (by omega)
        rw [e]
        simp

/-- The export rule: a resize to the same size is always fine; any other resize of an object
with exports raises `BufferError("Existing exports of data: object cannot be re-sized")`,
checked after the `ValueError` for a negative size. With no exports, a size that fits
in memory succeeds. -/
def ExportRule : Prop :=
  (∀ b : BA, baResize b b.size = .ok b) ∧
  (∀ (b : BA) (n : Int), 0 ≤ n → n ≠ b.size → b.exports > 0 →
    baResize b n = .error (bufferError "Existing exports of data: object cannot be re-sized")) ∧
  (∀ (b : BA) (n : Int), n < 0 → ∃ m, baResize b n = .error (.valueError m)) ∧
  (∀ (b : BA) (n : Int), 0 ≤ n → b.exports = 0 → n < 2 ^ 46 →
    ∃ r, baResize b n = .ok r ∧ r.data = (if n = b.size then b.data else resizedData b.data n) ∧
      r.exports = b.exports)

theorem bytesResizeCheck_small (old new : Int) (h0 : 0 ≤ new) (hs : new + 33 < 2 ^ 47) :
    bytesResizeCheck old new = .ok () := by
  have hc := bytesSizeCheck_ok new h0 hs
  unfold bytesResizeCheck
  rw [if_neg (by omega)]
  repeat' split
  all_goals first | rfl | exact hc

theorem baResizeAlloc_ok (b : BA) (n : Int) (h0 : 0 ≤ n) (h1 : n < 2 ^ 46) :
    ∃ p, baResizeAlloc b n = .ok p := by
  unfold baResizeAlloc
  split
  · exact ⟨_, rfl⟩
  · cases hn : baNewAlloc b.alloc b.offset n with
    | none => exact ⟨_, rfl⟩
    | some x =>
      have hge := baNewAlloc_ge _ _ _ _ h0 hn
      have hle := baNewAlloc_le _ _ _ _ h0 hn
      have h8 : n / 8 ≤ n := Int.ediv_le_self _ h0
      have hs : x + 33 < 2 ^ 47 := by omega
      have h2 : ¬ (x > baSizeMax) := by
        unfold baSizeMax
        rw [ssizeMax_val, objsize_val]
        omega
      have hc : baStorageCheck b.alloc x = .ok () := by
        unfold baStorageCheck
        rw [if_neg h2]
        exact bytesResizeCheck_small _ _ (by omega) hs
      simp only [hc]
      exact ⟨_, rfl⟩

theorem exportRule_proven : ExportRule := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b
    have : ¬ (b.size < 0) := by simp only [BA.size]; omega
    simp [baResize, this, pure, Except.pure]
  · intro b n h0 hn hx
    have h1 : ¬ (n < 0) := by omega
    simp [baResize, h1, hn, canResize, hx, bind, Except.bind]
  · intro b n h
    exact ⟨_, by simp [baResize, h, bind, Except.bind]; rfl⟩
  · intro b n h0 hE h1
    have hn : ¬ (n < 0) := by omega
    by_cases he : n = b.size
    · refine ⟨b, ?_, by simp [he], rfl⟩
      subst he
      simp [baResize, hn, pure, Except.pure, bind, Except.bind]
    · obtain ⟨⟨a, o⟩, hp⟩ := baResizeAlloc_ok b n h0 h1
      refine ⟨{ b with data := resizedData b.data n, alloc := a, offset := o }, ?_, by simp [he], rfl⟩
      unfold baResize
      simp [bind, Except.bind, pure, Except.pure, hn, he, canResize, hE, hp]

/-! ## What the failure paths leave -/

theorem initFast_values : ∀ (rest : List Obj) (i : Nat) (cur : BA) (pre : List Int),
    cur.data = pre ++ List.replicate rest.length uninit → pre.length = i → (∀ x ∈ pre, x ≠ uninit) →
    match baInitFast.go i cur rest with
    | .inl (b, _) => ∀ x ∈ b.data, x ≠ uninit
    | .inr () => True := by
  intro rest
  induction rest with
  | nil =>
    intro i cur pre hd hi hp
    simp only [baInitFast.go]
    simpa [hd] using hp
  | cons item rest ih =>
    intro i cur pre hd hi hp
    simp only [baInitFast.go]
    cases item
    case int v =>
      simp only
      cases hv : getByteValue (.int v) with
      | error e => simp [baReset]
      | ok value =>
        simp only
        apply ih (i + 1) _ (pre ++ [(value : Int)])
        · simp only [hd, List.length_cons, List.replicate_succ]
          subst hi
          simp
        · simp [hi]
        · intro x hx
          rcases List.mem_append.mp hx with h | h
          · exact hp x h
          · have : x = (value : Int) := by simpa using h
            subst this
            simp only [uninit]
            omega
    all_goals trivial

theorem initRun_values (o : Obj) : ∀ (items : List Obj) (cur : BA), (∀ x ∈ cur.data, x ≠ uninit) →
    ∀ x ∈ (baInit.run o cur items).1.data, x ≠ uninit := by
  intro items
  induction items with
  | nil =>
    intro cur h
    simp only [baInit.run]
    split <;> exact h
  | cons item rest ih =>
    intro cur h
    simp only [baInit.run]
    cases hl : baInitLoop cur [item] with
    | error e => simpa using h
    | ok next =>
      simp only
      apply ih
      simp only [baInitLoop] at hl
      split at hl
      · simp at hl
      · rename_i value hv
        split at hl
        · simp at hl
        · simp only [baInitLoop, Except.ok.injEq] at hl
          subst hl
          intro x hx
          rcases List.mem_append.mp hx with h1 | h1
          · exact h x h1
          · have : x = (value : Int) := by simpa using h1
            subst this
            simp only [uninit]
            omega

/-- No byte a failed `__init__` left is uninitialised: after any `b.__init__(items)` on a fresh
object, every byte is a value, because the fast path resets the object when an item is refused.
That reset is pinned by the second clause: with a refused `int` after good ones, the object is empty
and the exception is the refusal. -/
def InitInitialised : Prop :=
  (∀ items : List Obj, ∀ x ∈ (baInit {} (some (.list items)) none none).1.data, x ≠ uninit) ∧
  (∀ (xs : List Nat) (v : Int) (ys : List Obj), (∀ c ∈ xs, c < 256) → (v < 0 ∨ v ≥ 256) →
    ((xs.length + 1 + ys.length : Nat) : Int) < 2 ^ 46 →
    let r := baInit {} (some (.list (xs.map (fun c : Nat => Obj.int (c : Int)) ++ .int v :: ys))) none none
    r.1.data = [] ∧ r.1.alloc = 0 ∧ r.2 = some (.valueError "byte must be in range(0, 256)"))

theorem initFast_fail (v : Int) (ys : List Obj) (hv : v < 0 ∨ v ≥ 256) : ∀ (xs : List Nat) (i : Nat) (cur : BA),
    (∀ c ∈ xs, c < 256) →
    ∃ b, baInitFast.go i cur (xs.map (fun c : Nat => Obj.int (c : Int)) ++ .int v :: ys) =
      .inl (baReset b, some (.valueError "byte must be in range(0, 256)")) := by
  intro xs
  induction xs with
  | nil =>
    intro i cur _
    have hb : getByteValue (.int v) = .error (.valueError "byte must be in range(0, 256)") := by
      have h : v < 0 ∨ 256 ≤ v := by omega
      simp [getByteValue, Obj.index?, h]
    exact ⟨cur, by simp [baInitFast.go, hb]⟩
  | cons c cs ih =>
    intro i cur hc
    have h1 : c < 256 := hc c (by simp)
    have hb : getByteValue (.int c) = .ok c := by
      have h : ¬ ((c : Int) < 0 ∨ (c : Int) ≥ 256) := by omega
      simp [getByteValue, Obj.index?, h]
    obtain ⟨b, hg⟩ := ih (i + 1) { cur with data := cur.data.set i (c : Int) }
      (fun x hx => hc x (by simp [hx]))
    refine ⟨b, ?_⟩
    simp [baInitFast.go, hb, hg]

/-- `bytearray.__init__` of a list on a fresh object, unfolded. -/
theorem baInit_list (items : List Obj) : baInit {} (some (.list items)) none none =
    match baResize {} (items.length : Int) with
    | .error e => (({} : BA), some e)
    | .ok r =>
      match baInitFast r items with
      | .inl res => res
      | .inr () =>
        match (if r.size ≠ 0 then baResize r 0 else .ok r) with
        | .error e => (r, some e)
        | .ok r0 =>
          match getIterOr (.typeError s!"cannot convert 'list' object to bytearray") (.list items) with
          | .error e => (r0, some e)
          | .ok its => baInit.run (.list items) r0 its := rfl

theorem initInitialised_proven : InitInitialised := by
  refine ⟨?_, ?_⟩
  · intro items
    rw [baInit_list]
    cases hr : baResize {} (items.length : Int) with
    | error e => simp
    | ok r =>
      obtain ⟨_, hc⟩ := baResize_cases _ _ _ hr
      have hd : r.data = List.replicate items.length uninit ∧ r.exports = 0 := by
        rcases hc with ⟨rfl, he⟩ | ⟨_, _, hd, hx, _⟩
        · have h0 : items.length = 0 := by simp only [BA.size, List.length_nil] at he; omega
          simp [h0]
        · simp [hd, hx, resizedData]
      simp only
      have hv := initFast_values items 0 r [] (by simpa using hd.1) rfl (by simp)
      unfold baInitFast
      cases hg : baInitFast.go 0 r items with
      | inl res =>
        rw [hg] at hv
        exact hv
      | inr u =>
        simp only
        have h0 : ∀ r0, (if r.size ≠ 0 then baResize r 0 else .ok r) = .ok r0 → r0.data = [] := by
          intro r0 h
          split at h
          · obtain ⟨_, hc2⟩ := baResize_cases _ _ _ h
            rcases hc2 with ⟨rfl, he⟩ | ⟨_, _, hd2, _, _⟩
            · have : r0.data.length = 0 := by simp only [BA.size] at he; omega
              exact List.length_eq_zero_iff.mp this
            · simp [hd2, resizedData]
          · rename_i hz
            simp only [Except.ok.injEq] at h
            subst h
            have : r.data.length = 0 := by simp only [BA.size] at hz; omega
            exact List.length_eq_zero_iff.mp this
        have hok : ∃ r0, (if r.size ≠ 0 then baResize r 0 else .ok r) = .ok r0 := by
          split
          · obtain ⟨r0, h1, _⟩ := exportRule_proven.2.2.2 r 0 (by omega) hd.2 (by decide)
            exact ⟨r0, h1⟩
          · exact ⟨r, rfl⟩
        obtain ⟨r0, hr0⟩ := hok
        rw [hr0]
        have hz := h0 r0 hr0
        simp only
        split
        · simp [hz]
        · apply initRun_values
          simp [hz]
  · intro xs v ys hxs hv hsize
    simp only
    rw [baInit_list]
    obtain ⟨r, hr, _⟩ := exportRule_proven.2.2.2 {} ((xs.map (fun c : Nat => Obj.int (c : Int)) ++ .int v :: ys).length : Int)
      (by omega) rfl (by simp only [List.length_append, List.length_map, List.length_cons]; omega)
    rw [hr]
    simp only
    obtain ⟨b, hb⟩ := initFast_fail v ys hv xs 0 r hxs
    unfold baInitFast
    rw [hb]
    simp [baReset]

/-- `extend` of a buffer whatever the argument's `__buffer__` does to `self`, into `m`: the bytes go
in at the old end clamped to the new one, so a `__buffer__` that shrinks `self` leaves no gap
(gh-153578). The example pins the clamp: a `__buffer__` that clears `self` leaves just the value. -/
def ExtendInitialised : Prop :=
  (∀ (self m r : BA) (v : Seq) (mutate : BA → Py BA), mutate self = .ok m →
    baExtendBuffer self { bytes := v, mutate } = .ok r →
    let lo := (min self.size m.size).toNat
    r.data = m.data.take lo ++ seqData v ++ m.data.drop lo) ∧
  baExtendBuffer (baOf [97]) { bytes := [120], mutate := baClear } =
    .ok { data := [120], alloc := 1, offset := 0, exports := 0 }

/-- Nothing `PyByteArray_FromStringAndSize` can fail on leaves a half-made object: `ob_exports` is
set before the allocation, so a new object has none and `bytearray_dealloc` reports nothing. A
success has the size asked for in a bytes object of that size; the failures are those of
`_PyBytes_FromSize`. -/
def AllocFailureSilent : Prop :=
  (∀ (bytes : Option Seq) (size : Int) (r : BA), baFromStringAndSize bytes size = .ok r →
    r.exports = 0 ∧ r.offset = 0 ∧ r.alloc = size ∧ baDealloc r.exports = []) ∧
  (∀ (bytes : Option Seq) (size : Int), size > baSizeMax →
    baFromStringAndSize bytes size = .error (.overflowError "byte string is too large")) ∧
  (∀ (bytes : Option Seq) (size : Int), size ≤ baSizeMax → size + 33 ≥ 2 ^ 47 →
    baFromStringAndSize bytes size = .error memoryError) ∧
  (∀ e : Int, baDealloc e = if e > 0 then ["SystemError: deallocated bytearray object has exported buffers"] else [])

theorem allocFailureSilent_proven : AllocFailureSilent := by
  refine ⟨?_, ?_, ?_, fun _ => rfl⟩
  · intro bytes size r h
    unfold baFromStringAndSize at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp only [Except.ok.injEq] at h
          subst h
          rename_i hz
          simp [baDealloc, hz]
        · simp only [Except.ok.injEq] at h
          subst h
          simp [baDealloc]
  · intro bytes size h
    have h1 : ¬ (size < 0) := by
      unfold baSizeMax at h
      rw [ssizeMax_val, objsize_val] at h
      omega
    have h2 : bytesSizeCheck size = .error (.overflowError "byte string is too large") := by
      unfold baSizeMax at h
      unfold bytesSizeCheck
      rw [if_neg (by rw [ssizeMax_val, objsize_val] at h; omega), if_pos h]
    simp [baFromStringAndSize, h1, h2]
  · intro bytes size h1 h2
    have hs : ¬ (size < 0) := by omega
    have h3 : bytesSizeCheck size = .error memoryError := by
      unfold baSizeMax at h1
      unfold bytesSizeCheck
      have hm : mallocFails (bytesObjectSize + size) = true := by
        rw [objsize_val]
        simp only [mallocFails, decide_eq_true_eq]
        omega
      rw [if_neg (by omega), if_neg (by omega)]
      simp [hm]
    simp [baFromStringAndSize, hs, h3]

/-- `bytearray.__alloc__()` and `__sizeof__()`: the count of the bytes object when there is storage,
nothing otherwise, and the object size on top; so an object with data reports at least its data and
the header of the bytes object. Hypothesis: a valid layout. -/
def AllocSizeofSpec : Prop :=
  (∀ b : BA, baAllocMethod b = if b.alloc > 0 then b.alloc + 33 else 0) ∧
  (∀ b : BA, baSizeof b = baBasicSize + baAllocMethod b) ∧
  (∀ b : BA, b.WF → 0 < b.size → b.size + 33 ≤ baAllocMethod b)

theorem allocSizeofSpec_proven : AllocSizeofSpec := by
  refine ⟨fun b => rfl, ?_, ?_⟩
  · intro b
    simp only [baSizeof, baAllocMethod]
    split
    · omega
    · omega
  · intro b hw h
    have h1 := hw.1
    have h2 := hw.2
    have hp : b.alloc > 0 := by omega
    simp only [baAllocMethod, if_pos hp, objsize_val]
    omega

/-- A failed `bytearray_resize_lock_held` keeps the contents and a valid layout, and sets the offset
to 0 when `bytearray_resize_storage` had started; `baResizeLeft` is that state. -/
def ResizeFailureLayout : Prop :=
  ∀ (b : BA) (n : Int) (e : PyExc), b.WF → baResize b n = .error e →
    (baResizeLeft b n).data = b.data ∧ (baResizeLeft b n).WF

theorem resizeFailureLayout_proven : ResizeFailureLayout := by
  intro b n e hw _
  have h1 := hw.1
  have h2 := hw.2
  unfold baResizeLeft
  split
  · exact ⟨rfl, hw⟩
  · split
    · exact ⟨rfl, hw⟩
    · split
      · exact ⟨rfl, hw⟩
      · refine ⟨rfl, by simp [BA.WF, BA.size] at h1 h2 ⊢; omega⟩

/-- A failed `del b[:k]` leaves a valid layout. Refuted: the failure path subtracts the shrink from an
`ob_start` that `bytearray_resize_storage` already reset, so the data starts before the allocation.
Hypotheses: a valid layout, and a shrink that leaves data. -/
def ShrinkFailureKeepsLayout : Prop :=
  ∀ (b r : BA) (growth : Int), b.WF → growth < 0 → 0 < b.size + growth →
    baShrinkStartFailure b growth = some r → r.WF

def shrinkExample : BA := { data := List.replicate 10 0, alloc := 10 }

theorem shrinkFailureKeepsLayout_refuted : ¬ ShrinkFailureKeepsLayout := by
  intro h
  have hr : baShrinkStartFailure shrinkExample (-8) = some { shrinkExample with offset := -8 } := by
    decide
  have := h shrinkExample _ (-8) (by decide) (by decide) (by decide) hr
  exact absurd this.1 (by decide)

end PyLean.BytesObj.Bytes
