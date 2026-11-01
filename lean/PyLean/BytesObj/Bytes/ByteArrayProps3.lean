import PyLean.BytesObj.Bytes.ByteArrayProps2

/-!
`bytearray`: slice assignment against `list`, mutating methods, the constructor, the
iterator and the read-only wrappers.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch
open PyLean.RangeSlice (Slice)

/-! ## Mutators -/

theorem getByte_ok (c : Nat) (hc : c < 256) : getByteValue (.int c) = .ok c := by
  have h : ¬ ((c : Int) < 0 ∨ (c : Int) ≥ 256) := by omega
  simp [getByteValue, Obj.index?, h]

theorem getByte_bad (v : Int) (h : v < 0 ∨ v ≥ 256) :
    getByteValue (.int v) = .error (.valueError "byte must be in range(0, 256)") := by
  simp [getByteValue, Obj.index?, h]

theorem resize_small (b : BA) (n : Int) (h0 : 0 ≤ n) (hE : b.exports = 0) (h1 : n < 2 ^ 46)
    (h2 : b.alloc < 2 ^ 46) : ∃ r, baResize b n = .ok r := by
  obtain ⟨r, hr, _⟩ := exportRule_proven.2.2.2 b n h0 hE h1 h2
  exact ⟨r, hr⟩

/-- `append`, `insert` and `pop` act on the contents as the `list` methods do (the object
has no exports, and fits in memory; an argument byte in `range(256)`): the bounds logic of
`insert` and `pop` is the list's for every int index. An item outside `range(256)` raises
`ValueError` first. `reverse` is an involution and `clear` empties. -/
def MutatorsSpec : Prop :=
  (∀ (b : BA) (c : Nat), c < 256 → b.exports = 0 → b.size < 2 ^ 45 → b.alloc < 2 ^ 45 →
    ∃ r, baAppend b (.int c) = .ok r ∧ r.data = Sequences.listAppend b.data c) ∧
  (∀ (b : BA) (i : Int) (c : Nat), c < 256 → b.exports = 0 → b.size < 2 ^ 45 → b.alloc < 2 ^ 45 →
    ssizeMin ≤ i → i ≤ ssizeMax →
    ∃ r, baInsert b i (.int c) = .ok r ∧ Sequences.listInsert b.data i c = .ok r.data) ∧
  (∀ (b r : BA) (i : Option Int) (v : Int), baPop b i = .ok (v, r) →
    Sequences.listPop b.data i = .ok (v, r.data)) ∧
  (∀ (b : BA) (v : Int), v < 0 ∨ v ≥ 256 →
    baAppend b (.int v) = .error (.valueError "byte must be in range(0, 256)")) ∧
  (∀ b : BA, (baReverse (baReverse b)).data = b.data ∧ (baReverse b).data.length = b.data.length) ∧
  (∀ (b r : BA), baClear b = .ok r → r.data = [])

theorem baPop_list (b r : BA) (i : Option Int) (v : Int) (h : baPop b i = .ok (v, r)) :
    Sequences.listPop b.data i = .ok (v, r.data) := by
  have hsz : b.size = (b.data.length : Int) := rfl
  unfold baPop at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases h1 : Sequences.popArg i with
  | error e => rw [h1] at h; simp at h
  | ok idx =>
  rw [h1] at h
  simp only at h
  by_cases hn : b.size = 0
  · simp [hn] at h
  rw [if_neg hn] at h
  by_cases hb : (if idx < 0 then idx + b.size else idx) < 0 ∨
      (if idx < 0 then idx + b.size else idx) ≥ b.size
  · rw [if_pos hb] at h
    simp at h
  rw [if_neg hb] at h
  split at h
  · simp at h
  rename_i hc
  split at h
  · simp at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨e1, e2⟩ := h
  subst e1
  subst e2
  have hnz : b.data.length ≠ 0 := by omega
  simp only [Sequences.listPop, bind, Except.bind, h1, Sequences.listPopK, pure, Except.pure]
  have hv : Sequences.validIndex (if idx < 0 then idx + b.data.length else idx) b.data.length = true := by
    simp only [Sequences.validIndex, decide_eq_true_eq]
    rw [hsz] at hb
    omega
  simp [hnz, hv, Sequences.ix, hsz]

theorem mutatorsSpec_proven : MutatorsSpec := by
  refine ⟨?_, ?_, baPop_list, ?_, ?_, ?_⟩
  · intro b c hc hE hs ha
    obtain ⟨r, hr⟩ := resize_small b (b.size + 1) (by simp only [BA.size]; omega) hE (by omega) (by omega)
    refine ⟨{ r with data := b.data ++ [(c : Int)] }, ?_, rfl⟩
    have hne : ¬ (b.size = ssizeMax) := by
      rw [ssizeMax_val]; omega
    simp [baAppend, getByte_ok c hc, hne, hr, bind, Except.bind, pure, Except.pure]
  · intro b i c hc hE hs ha h1 h2
    obtain ⟨r, hr⟩ := resize_small b (b.size + 1) (by simp only [BA.size]; omega) hE (by omega) (by omega)
    have hne : ¬ (b.size = ssizeMax) := by
      rw [ssizeMax_val]; omega
    have hi : Sequences.asSsize i = .ok i := by
      simp [Sequences.asSsize, h1, h2]
    refine ⟨{ r with data := Sequences.insAt b.data (Sequences.ins1Pos b.size i).toNat (c : Int) }, ?_, ?_⟩
    · simp only [baInsert, hi, getByte_ok c hc, hne, if_false, hr, bind, Except.bind, pure, Except.pure]
    · simp only [Sequences.listInsert, hi, bind, Except.bind, pure, Except.pure, Sequences.listIns1]
      rfl
  · intro b v h
    simp only [baAppend, getByte_bad v h, bind, Except.bind]
  · intro b
    simp [baReverse]
  · intro b r h
    unfold baClear at h
    obtain ⟨h0, hc⟩ := baResize_cases b r 0 h
    rcases hc with ⟨rfl, hn⟩ | ⟨_, _, hd, _, _⟩
    · have : r.data.length = 0 := by simp only [BA.size] at hn; omega
      exact List.length_eq_zero_iff.mp this
    · simp [hd, resizedData]

/-! ## Initialisation layout -/

/-- One append of the slow path of `__init__` keeps a valid buffer layout: refuted, the
test `Py_SIZE(self) + 1 < self->ob_alloc` does not subtract `ob_start - ob_bytes`, which an
iterator can move. -/
def InitLoopKeepsLayout : Prop :=
  ∀ (b r : BA) (item : Obj), b.WF → baInitLoop b [item] = .ok r → r.WF

theorem initLoopKeepsLayout_refuted : ¬ InitLoopKeepsLayout := by
  intro h
  have hw : BA.WF { data := [1], alloc := 5, offset := 3 } := by
    simp [BA.WF, BA.size]
  have hr : baInitLoop { data := [1], alloc := 5, offset := 3 } [.int 65] =
      .ok { data := [1, 65], alloc := 5, offset := 3 } := by
    decide
  have := h _ _ _ hw hr
  simp [BA.WF, BA.size] at this

/-- With `ob_start == ob_bytes` the same step keeps the layout: the offset is the whole
cause, and a fresh object, which no iterator touched, is safe. -/
def InitLoopFreshLayout : Prop :=
  ∀ (b r : BA) (item : Obj), b.WF → b.offset = 0 → baInitLoop b [item] = .ok r → r.WF

theorem initLoopFreshLayout_proven : InitLoopFreshLayout := by
  intro b r item hw h0 h
  have hsz : b.size = (b.data.length : Int) := rfl
  simp only [baInitLoop] at h
  cases hv : getByteValue item with
  | error e => simp [hv] at h
  | ok value =>
    simp only [hv] at h
    by_cases hc : b.size + 1 < b.alloc
    · rw [if_pos hc] at h
      simp only [Except.ok.injEq] at h
      subst h
      refine ⟨by simpa using hw.1, Or.inr ?_⟩
      simp only [BA.size, List.length_append, List.length_cons, List.length_nil]
      simp only [h0]
      omega
    · rw [if_neg hc] at h
      split at h
      · simp at h
      rename_i r' hr
      simp only [Except.ok.injEq] at h
      subst h
      obtain ⟨hw2, hs2, _, _⟩ := resizeWF_proven b r' _ hw hr
      refine ⟨hw2.1, Or.inr ?_⟩
      simp only [BA.size] at hs2 ⊢
      simp only [List.length_append, List.length_cons, List.length_nil]
      rcases hw2.2 with ⟨_, h2, _⟩ | h2
      · rw [h2] at hs2
        simp at hs2
        omega
      · simp only [BA.size, hs2] at h2
        omega

/-! ## Slice assignment against `list` -/

/-- `b[s] = v` succeeds only where `list[s] = v` does, with the same contents. Refuted by
the empty extended-slice assignment, which deletes
(`bugs/sequences-array-extended-slice-empty-deletes.yaml`, the same code shape in `array`). -/
def SliceAssignAgreesList : Prop :=
  ∀ (b r : BA) (sl : Slice) (v : Seq), baAssSlice b sl (some (.bytes v)) = .ok r →
    Sequences.listAssSubscript b.data sl (some (seqData v)) = .ok r.data

theorem sliceAssignAgreesList_refuted : ¬ SliceAssignAgreesList := by
  intro h
  have hr : baAssSlice (baOf [1, 2, 3]) ⟨none, none, some 2⟩ (some (.bytes [])) =
      .ok { data := [2], alloc := 2, offset := 0, exports := 0 } := by
    decide
  have := h _ _ _ _ hr
  revert this
  decide

/-- `start` and `stop` of a plain slice lie in `[0, n]`. -/
theorem adjust_plain (x n : Int) (hn : 0 ≤ n) :
    0 ≤ RangeSlice.adjustOne x n 1 ∧ RangeSlice.adjustOne x n 1 ≤ n := by
  simp only [RangeSlice.adjustOne]
  repeat' split
  all_goals omega

/-- A plain slice: the splice is `listAssSlice`. -/
theorem plain_agrees (b r : BA) (a c : Int) (bytes : List Int) (ha : 0 ≤ a) (hac : a ≤ c)
    (hc : c ≤ b.data.length) (h : baSetsliceLinear b a c bytes = .ok r) :
    r.data = Sequences.listAssSlice b.data a c bytes := by
  obtain ⟨l, rfl⟩ : ∃ l : Nat, a = l := ⟨a.toNat, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k : Nat, c = k := ⟨c.toNat, by omega⟩
  rw [setsliceSpec_proven b r l k bytes (by omega) (by omega) h]
  have h1 : ¬ ((l : Int) < 0) := by omega
  have h2 : ¬ ((l : Int) > b.data.length) := by omega
  have h3 : ¬ ((k : Int) < l) := by omega
  have h4 : ¬ ((k : Int) > b.data.length) := by omega
  simp [Sequences.listAssSlice, h1, h2, h3, h4]

/-- The narrowed statement: with a non-empty value, every successful `b[s] = v` leaves the
contents `list[s] = v` leaves, for all slices with int parts, extended ones included. -/
def SliceAssignAgreesNonempty : Prop :=
  ∀ (b r : BA) (sl : Slice) (v : Seq), v ≠ [] →
    baAssSlice b sl (some (.bytes v)) = .ok r →
    Sequences.listAssSubscript b.data sl (some (seqData v)) = .ok r.data

/-- Every successful `del b[s]` leaves the contents `del list[s]` leaves. -/
def SliceDeleteAgrees : Prop :=
  ∀ (b r : BA) (sl : Slice), baAssSlice b sl none = .ok r →
    Sequences.listAssSubscript b.data sl none = .ok r.data

theorem assValue_bytes (b : BA) (v : Seq) : assValue b (some (.bytes v)) = .ok (some v) := by
  simp [assValue, Obj.isNumber, assValue.baFromObjectItems, Obj.buffer?]

/-- Shared unfolding of the two proofs. -/
theorem baAssSlice_unfold (b r : BA) (sl : Slice) (val : Option Obj) (vals : Option Seq)
    (hv : assValue b val = .ok vals) (h : baAssSlice b sl val = .ok r) :
    ∃ st sp se a c len, RangeSlice.sliceUnpack sl = .ok (st, sp, se) ∧
      RangeSlice.adjustIndices (b.data.length : Int) st sp se = (a, c, len) ∧
      (let c' := if (se < 0 ∧ a < c) ∨ (se > 0 ∧ a > c) then a else c
       let bytes := seqData (vals.getD [])
       (if se = 1 then baSetsliceLinear b a c' bytes else baAssExtended b a c' se len bytes) = .ok r) := by
  unfold baAssSlice at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases hu : RangeSlice.sliceUnpack sl with
  | error e => rw [hu] at h; simp at h
  | ok t =>
    rw [hu] at h
    obtain ⟨st, sp, se⟩ := t
    simp only at h
    have hsz : b.size = (b.data.length : Int) := rfl
    rw [hsz] at h
    cases hadj : RangeSlice.adjustIndices (b.data.length : Int) st sp se with
    | mk a rest =>
      obtain ⟨c, len⟩ := rest
      rw [hadj] at h
      simp only [hv] at h
      exact ⟨st, sp, se, a, c, len, rfl, hadj, h⟩

theorem sliceAssignAgreesNonempty_proven : SliceAssignAgreesNonempty := by
  intro b r sl v hne h
  obtain ⟨st, sp, se, a, c, len, hu, hadj, hmain⟩ :=
    baAssSlice_unfold b r sl _ _ (assValue_bytes b v) h
  simp only [Option.getD_some] at hmain
  have hL : (seqData v).length ≠ 0 := by
    simpa [seqData] using hne
  simp only [Sequences.listAssSubscript, Sequences.adjustSlice, bind, Except.bind, hu, pure, Except.pure]
  rw [hadj]
  simp only
  by_cases hs : se = 1
  · subst hs
    rw [if_pos rfl] at hmain
    have hpair : a = RangeSlice.adjustOne st (b.data.length : Int) 1 ∧
        c = RangeSlice.adjustOne sp (b.data.length : Int) 1 := by
      simp only [RangeSlice.adjustIndices, Prod.mk.injEq] at hadj
      exact ⟨hadj.1.symm, hadj.2.1.symm⟩
    have ra := adjust_plain st b.data.length (by omega)
    have rc := adjust_plain sp b.data.length (by omega)
    rw [← hpair.1] at ra
    rw [← hpair.2] at rc
    have e := plain_agrees b r a _ _ ra.1 (by split <;> omega) (by split <;> omega) hmain
    simp [e]
  · rw [if_neg hs] at hmain
    unfold baAssExtended at hmain
    simp only [bind, Except.bind, pure, Except.pure] at hmain
    have hN : ¬ (((seqData v).length : Int) = 0) := by omega
    rw [if_neg hN] at hmain
    split at hmain
    · simp at hmain
    rename_i hlen
    simp only [Except.ok.injEq] at hmain
    subst hmain
    have hl2 : ¬ (((seqData v).length : Int) ≠ len) := hlen
    have hl3 : (seqData v).length = len := by omega
    have hl4 : ¬ (len = 0) := by omega
    simp [hs, hl3, hl4]

theorem sliceDeleteAgrees_proven : SliceDeleteAgrees := by
  intro b r sl h
  have hv : assValue b none = .ok none := rfl
  obtain ⟨st, sp, se, a, c, len, hu, hadj, hmain⟩ := baAssSlice_unfold b r sl _ _ hv h
  simp only [Option.getD_none, seqData, List.map_nil] at hmain
  simp only [Sequences.listAssSubscript, Sequences.adjustSlice, bind, Except.bind, hu, pure, Except.pure]
  rw [hadj]
  simp only
  by_cases hs : se = 1
  · subst hs
    rw [if_pos rfl] at hmain
    have hpair : a = RangeSlice.adjustOne st (b.data.length : Int) 1 ∧
        c = RangeSlice.adjustOne sp (b.data.length : Int) 1 := by
      simp only [RangeSlice.adjustIndices, Prod.mk.injEq] at hadj
      exact ⟨hadj.1.symm, hadj.2.1.symm⟩
    have ra := adjust_plain st b.data.length (by omega)
    have rc := adjust_plain sp b.data.length (by omega)
    rw [← hpair.1] at ra
    rw [← hpair.2] at rc
    have e := plain_agrees b r a _ _ ra.1 (by split <;> omega) (by split <;> omega) hmain
    simp [e]
  · rw [if_neg hs] at hmain
    have hlenN : 0 ≤ len := by
      have := Sequences.adjust_len_nonneg (b.data.length : Int) st sp se
      rw [hadj] at this
      exact this
    unfold baAssExtended at hmain
    simp only [bind, Except.bind, pure, Except.pure, List.length_nil] at hmain
    simp only [Int.natCast_zero, if_true] at hmain
    split at hmain
    · simp at hmain
    rename_i hc
    by_cases hz : len = 0
    · simp only [hz, if_true, Except.ok.injEq] at hmain
      subst hmain
      simp [hs, hz]
    · simp only [hz, if_false] at hmain
      have hlen2 : ¬ (len ≤ 0) := by omega
      simp only [hs, if_false, hlen2]
      cases hd : Sequences.delExtended b.data a _ se len with
      | error e =>
        rw [hd] at hmain
        simp at hmain
      | ok mem =>
        rw [hd] at hmain
        simp only at hmain
        split at hmain
        · simp at hmain
        simp only [Except.ok.injEq] at hmain
        subst hmain
        rfl

end PyLean.BytesObj.Bytes
