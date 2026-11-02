import PyLean.BytesObj.Bytes.Fallible

/-!
`take_bytes`, the end of a `PyBytesWriter`, `_PyBytes_ResizeKeepOnError` and `bytes_iteritem`.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-! ## `take_bytes` -/

theorem baTake_ok (b : BA) (k : Int) (hE : b.exports = 0) (h0 : 0 < k) (h1 : k ≤ b.size)
    (hs : b.size + 33 < 2 ^ 47) :
    baTakeCore b k = .ok (((b.data.take k.toNat).map Int.toNat),
      if k < b.size - k then { b with data := b.data.drop k.toNat, offset := b.offset + k }
      else { b with data := b.data.drop k.toNat, alloc := b.size - k, offset := 0 }) := by
  unfold baTakeCore
  have hz : ¬ (b.size = 0) := by omega
  have hk : ¬ (k = 0) := by omega
  have hr : ¬ (k < 0 ∨ k > b.size) := by omega
  simp only [bind, Except.bind, pure, Except.pure, hr, if_false, canResize, hE, gt_iff_lt,
    Nat.lt_irrefl, hk, hz, false_or]
  by_cases hc : k < b.size - k
  · simp [hc, bytesSizeCheck_ok k (by omega) (by omega)]
  · simp [hc, bytesSizeCheck_ok (b.size - k) (by omega) (by omega),
      bytesResizeCheck_small b.alloc k (by omega) (by omega)]

/-- `b.take_bytes(n)`: a count in `0..len(b)` gives the first bytes and leaves the rest, whichever of
the two ways round it copies, in a valid layout; a count that is out of range is the `IndexError`,
named after the size; an export is the `BufferError`, and a count of 0 refuses nothing. Hypotheses:
a valid layout, no exports for the success, and sizes an object can have. -/
def TakeBytesSpec : Prop :=
  (∀ (b : BA) (k : Int), b.WF → b.exports = 0 → 0 < k → k ≤ b.size → b.size + 33 < 2 ^ 47 →
    ∃ r, baTakeCore b k = .ok ((b.data.take k.toNat).map Int.toNat, r) ∧
      r.data = b.data.drop k.toNat ∧ r.WF ∧ r.exports = 0) ∧
  (∀ (b : BA) (k : Int), k < 0 ∨ k > b.size →
    baTakeCore b k = .error (.indexError s!"can't take {k} bytes outside size {b.size}")) ∧
  (∀ (b : BA) (k : Int), 0 ≤ k → k ≤ b.size → b.exports > 0 →
    baTakeCore b k = .error (bufferError "Existing exports of data: object cannot be re-sized")) ∧
  (∀ (b : BA), b.exports = 0 → baTakeCore b 0 = .ok ([], b)) ∧
  (∀ (b : BA) (v : Int), ssizeMin ≤ v → v ≤ ssizeMax →
    baTakeBytes b (.int v) = baTakeCore b (if v < 0 then v + b.size else v)) ∧
  (∀ b : BA, baTakeBytes b .none = baTakeCore b b.size) ∧
  (∀ (b : BA) (e : PyExc), baTakeBytes b (.indexRaises e) = .error e) ∧
  (∀ (b : BA) (s : Seq), baTakeBytes b (.bytes s) = .error (.typeError "n must be an integer or None")) ∧
  (∀ (b : BA) (v : Int), v > ssizeMax →
    baTakeBytes b (.int v) = .error (.indexError "cannot fit 'int' into an index-sized integer"))

theorem takeBytesSpec_proven : TakeBytesSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b k hw hE h0 h1 hs
    have h2 := hw.1
    have h3 := hw.2
    refine ⟨_, baTake_ok b k hE h0 h1 hs, ?_, ?_, ?_⟩
    · split <;> rfl
    · have hl : ((b.data.drop k.toNat).length : Int) = b.size - k := by
        simp only [List.length_drop, BA.size] at *
        omega
      split
      · exact ⟨by simp; omega, by simp only [BA.size] at *; omega⟩
      · exact ⟨by simp, by simp only [BA.size] at *; omega⟩
    · split <;> exact hE
  · intro b k h
    simp [baTakeCore, h, bind, Except.bind]
    rfl
  · intro b k h0 h1 h2
    have hr : ¬ (k < 0 ∨ k > b.size) := by omega
    simp [baTakeCore, hr, canResize, h2, bind, Except.bind]
  · intro b hE
    have hp : ¬ (0 > b.size) := by simp only [BA.size]; omega
    simp [baTakeCore, canResize, hE, bind, Except.bind, pure, Except.pure, hp]
  · intro b v h1 h2
    have hc : takeCount (.int v) v = .ok v := by simp [takeCount, h1, h2]
    simp [baTakeBytes, Obj.index?, hc, bind, Except.bind, pure, Except.pure]
  · intro b
    simp [baTakeBytes, bind, Except.bind, pure, Except.pure]
  · intro b e
    rfl
  · intro b s
    rfl
  · intro b v h
    have hc : ¬ (ssizeMin ≤ v ∧ v ≤ ssizeMax) := by omega
    simp [baTakeBytes, Obj.index?, takeCount, hc, bind, Except.bind, Obj.typeName]
    rfl

/-! ## The end of a writer -/

/-- `PyBytesWriter_FinishWithSize`: a negative size and one above `size` are the two `ValueError`s,
and a writer as `Create` left it can be finished at any size up to its own, for either result type.
The final resize only goes down, so it does not fail. `FinishWithPointer` gives back what the caller
wrote, and refuses more than `size`. Hypothesis: the size of an object that can exist. -/
def WriterFinish : Prop :=
  (∀ (w : Writer) (k : Int), k < 0 →
    writerFinishSize w k = .error (.valueError "size must be positive")) ∧
  (∀ (w : Writer) (k : Int), 0 ≤ k → k > w.size →
    writerFinishSize w k = .error (.valueError "size larger than allocated size")) ∧
  (∀ (n k : Int) (ba : Bool), 0 ≤ n → n + 33 < 2 ^ 47 → 0 ≤ k → k ≤ n →
    ∃ w, writerCreate n ba = .ok w ∧ w.size = n ∧ writerFinishSize w k = .ok ()) ∧
  (∀ (w : Writer) (out : Seq), writerFinishSize w out.length = .ok () → writerFinish w out = .ok out) ∧
  (∀ (w : Writer) (out : Seq), (out.length : Int) > w.size →
    writerFinish w out = .error (.valueError "size larger than allocated size"))

theorem writerFinish_proven : WriterFinish := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w k h
    simp [writerFinishSize, h]
  · intro w k h0 h
    have h1 : ¬ (k < 0) := by omega
    simp [writerFinishSize, h1, h]
  · intro n k ba h0 hs h1 h2
    have hc (m : Int) (hm : 0 ≤ m) (hm2 : m ≤ n) := bytesSizeCheck_ok m hm (by omega)
    have hk : ¬ (k < 0) := by omega
    have hg : ¬ (k > n) := by omega
    by_cases hn : n ≥ 1
    · by_cases hsm : n ≤ smallBufferSize
      · refine ⟨{ size := n, useBytearray := ba, overallocate := !ba }, ?_, rfl, ?_⟩
        · simp [writerCreate, show ¬ (n < 0) by omega, hn, writerResizeRaw, writerAllocated, hsm]
        · simp [writerFinishSize, hk, hg, hc k h1 h2]
      · have hobj : writerObjResize { useBytearray := ba, overallocate := !ba } n = .ok (n, n) := by
          simp [writerObjResize, hc n h0 (by omega)]
        refine ⟨{ obj := some (n, n), size := n, useBytearray := ba, overallocate := !ba }, ?_, rfl, ?_⟩
        · simp [writerCreate, show ¬ (n < 0) by omega, hn, writerResizeRaw, writerAllocated, hsm, hobj]
        · unfold writerFinishSize
          rw [if_neg hk, if_neg hg]
          split
          · rfl
          · simp only
            cases ba with
            | false =>
              simp only [Bool.false_eq_true, if_false]
              split
              · exact bytesResizeCheck_small _ _ h1 (by omega)
              · rfl
            | true =>
              simp only [if_true]
              split
              · cases hna : baNewAlloc n 0 k with
                | none => rfl
                | some x =>
                  have hx : x = k := by
                    unfold baNewAlloc at hna
                    repeat' split at hna
                    all_goals simp_all
                    all_goals omega
                  subst hx
                  simp only
                  unfold baStorageCheck
                  rw [if_neg (by unfold baSizeMax; rw [ssizeMax_val, objsize_val]; omega)]
                  exact bytesResizeCheck_small _ _ h1 (by omega)
              · rfl
    · have hz : n = 0 := by omega
      have hk0 : k = 0 := by omega
      subst hz
      subst hk0
      refine ⟨{ useBytearray := ba, overallocate := !ba }, ?_, rfl, ?_⟩
      · simp [writerCreate]
      · cases ba <;> simp [writerFinishSize, bytesSizeCheck]
  · intro w out h
    simp [writerFinish, h]
  · intro w out h
    have h1 : ¬ ((out.length : Int) < 0) := by omega
    simp [writerFinish, writerFinishSize, h1, h]

/-- `PyBytesWriter_Format`: the size moves by the text `bytes_fromformat` writes at its old value; on
an error it stays there and nothing is added, which is the undo at bytesobject.c:4077-4081. -/
def WriterFormatRules : Prop :=
  ∀ (w w' : Writer) (f : Seq) (args : List CArg) (t : Seq) (e : Option PyExc),
    writerFormat w f args = (w', t, e) →
    (e = none → w'.size = w.size + t.length ∧ bytesFromFormat (f.takeWhile (· != 0)) args = .ok t) ∧
    (e ≠ none → w'.size = w.size ∧ t = [])

theorem writerResize_size (w w' : Writer) (n : Int) (h : writerResize w n = .ok w') : w'.size = n := by
  unfold writerResize at h
  split at h
  · simp at h
  · split at h
    · split at h
      · simp only [Except.ok.injEq] at h
        rw [← h]
      · simp at h
    · simp only [Except.ok.injEq] at h
      rw [← h]

theorem writerFormatRules_proven : WriterFormatRules := by
  intro w w' f args t e h
  unfold writerFormat at h
  split at h
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨by simp, fun _ => ⟨rfl, rfl⟩⟩
  · split at h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨by simp, fun _ => ⟨rfl, rfl⟩⟩
    · rename_i text htext
      split at h
      · rename_i w2 hw2
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨fun _ => ⟨writerResize_size _ _ _ hw2, htext⟩, by simp⟩
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨by simp, fun _ => ⟨rfl, rfl⟩⟩

/-! ## `_PyBytes_ResizeKeepOnError` -/

/-- `_PyBytes_ResizeKeepOnError`: a negative size is refused, the same size and an empty result cannot
fail, and past that it fails as `_PyBytes_FromSize` does, whichever of the copy and
`bytes_resize_inplace` runs. `bytes_resize_inplace` checks the same size before its `realloc`. -/
def BytesResizeRules : Prop :=
  (∀ (o n : Int), n < 0 → ∃ m, bytesResizeCheck o n = .error (systemError m)) ∧
  (∀ n : Int, 0 ≤ n → bytesResizeCheck n n = .ok ()) ∧
  (∀ o : Int, bytesResizeCheck o 0 = .ok ()) ∧
  (∀ (o n : Int), o ≠ n → n > baSizeMax →
    bytesResizeCheck o n = .error (.overflowError "byte string is too large")) ∧
  (∀ (o n : Int), o ≠ n → n ≤ baSizeMax → n + 33 ≥ 2 ^ 47 →
    bytesResizeCheck o n = .error memoryError) ∧
  (∀ (o n : Int), 0 ≤ n → n + 33 < 2 ^ 47 → bytesResizeCheck o n = .ok ())

theorem bytesResizeRules_proven : BytesResizeRules := by
  have hmax : baSizeMax = 9223372036854775774 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, fun o n h0 h1 => bytesResizeCheck_small o n h0 h1⟩
  · intro o n h
    exact ⟨_, by simp [bytesResizeCheck, h]; rfl⟩
  · intro n h
    unfold bytesResizeCheck
    rw [if_neg (by omega), if_pos rfl]
  · intro o
    exact bytesResizeCheck_small o 0 (by omega) (by decide)
  · intro o n h1 h2
    have h3 : ¬ (n < 0) := by omega
    have h4 : bytesSizeCheck n = .error (.overflowError "byte string is too large") := by
      unfold bytesSizeCheck
      have h5 : n > ssizeMax - bytesObjectSize := h2
      rw [if_neg (by omega), if_pos h5]
    simp only [bytesResizeCheck, h3, h1, if_false]
    split
    · exact h4
    · split
      · omega
      · exact h4
  · intro o n h1 h2 h3
    have h4 : ¬ (n < 0) := by omega
    have h5 : bytesSizeCheck n = .error memoryError := by
      unfold bytesSizeCheck
      have h6 : ¬ (n > ssizeMax - bytesObjectSize) := by
        have : baSizeMax = ssizeMax - bytesObjectSize := rfl
        omega
      have hm : mallocFails (bytesObjectSize + n) = true := by
        rw [objsize_val]
        simp only [mallocFails, decide_eq_true_eq]
        omega
      rw [if_neg (by omega), if_neg h6]
      simp [hm]
    simp only [bytesResizeCheck, h4, h1, if_false]
    split
    · exact h5
    · split
      · omega
      · exact h5

/-! ## `*` at a specialized site -/

/-- A specialized `b * n` behaves as the generic one. Refuted: for an int outside `Py_ssize_t` the
class is the same and the message is not. In range the two agree. -/
def SpecializedRepeatAgrees : Prop :=
  ∀ (s : Seq) (n : Int), bytesMulSpecialized s n = bytesMul s n

set_option maxRecDepth 100000 in
theorem specializedRepeatAgrees_refuted : ¬ SpecializedRepeatAgrees := by
  intro h
  have := h [97] (2 ^ 63)
  revert this
  decide

/-- The narrowed statement: for a count in range the specialized `*` is the generic one. -/
def SpecializedRepeatInRange : Prop :=
  ∀ (s : Seq) (n : Int), ssizeMin ≤ n → n ≤ ssizeMax → bytesMulSpecialized s n = bytesMul s n

theorem specializedRepeatInRange_proven : SpecializedRepeatInRange := by
  intro s n h1 h2
  have h3 : ¬ (n < ssizeMin ∨ n > ssizeMax) := by omega
  have h4 : Sequences.repeatCount n = .ok n := by
    simp [Sequences.repeatCount, Sequences.asSsizeExc, h1, h2]
  simp [bytesMulSpecialized, bytesMul, h3, h4, bind, Except.bind]

/-! ## `for` over a `bytes` -/

/-- `bytes_iteritem(obj, index)`, bytesobject.c, the `_tp_iteritem` that `for` uses in place of the
iterator: the item and the next index, or none past the end. -/
def bytesIterItem (s : Seq) (index : Nat) : Option Nat × Nat :=
  if index ≥ s.length then (none, index) else (some (s.getD index 0), index + 1)

/-- Stepping `bytes_iteritem` gives what `striter_next` gives at each index. -/
def IterItemAgrees : Prop :=
  ∀ (s : Seq) (i : Nat),
    (bytesIterItem s i).1 = (striterNext { seq := some s, index := i }).1 ∧
    (i < s.length → (bytesIterItem s i).2 = i + 1) ∧ (s.length ≤ i → (bytesIterItem s i).2 = i)

theorem iterItemAgrees_proven : IterItemAgrees := by
  intro s i
  by_cases h : i < s.length
  · have h1 : ¬ (i ≥ s.length) := by omega
    have h2 : (i : Int) < s.length := by omega
    simp [bytesIterItem, striterNext, h1, h2, h]
  · have h1 : i ≥ s.length := by omega
    have h2 : ¬ ((i : Int) < s.length) := by omega
    simp [bytesIterItem, striterNext, h1, h2, h]

end PyLean.BytesObj.Bytes
