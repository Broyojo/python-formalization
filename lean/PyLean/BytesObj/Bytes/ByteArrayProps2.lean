import PyLean.BytesObj.Bytes.ByteArrayProps

/-!
`bytearray` slice assignment and mutating methods against their specification and
against `list`.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch
open PyLean.RangeSlice (Slice)

/-! ## The linear splice -/

theorem shrink_lists (d : List Int) (l b h : Nat) (hlb : l + b < h) (hh : h ≤ d.length) :
    let mem := d.take (l + b) ++ (d.drop h).take (d.length - h) ++ d.drop (l + b + (d.length - h))
    let t := l + b + (d.length - h)
    (mem.take t).take l = d.take l ∧ (mem.take t).drop (l + b) = d.drop h := by
  intro mem t
  have hA : (d.take (l + b)).length = l + b := by simp; omega
  have hB : ((d.drop h).take (d.length - h)) = d.drop h := List.take_of_length_le (by simp)
  have hM : mem.take t = d.take (l + b) ++ d.drop h := by
    simp only [mem, t, hB]
    exact List.take_left' (by simp; omega)
  rw [hM]
  constructor
  · rw [List.take_append_of_le_length (by omega), List.take_take]
    congr 1
    omega
  · exact List.drop_left' hA

theorem grow_lists (d : List Int) (pad : List Int) (l b h : Nat) (hh : h ≤ d.length) (hl : l ≤ h)
    (hsize : (d ++ pad).length = l + b + (d.length - h)) :
    let D := d ++ pad
    let mem := D.take (l + b) ++ (D.drop h).take (d.length - h) ++ D.drop (l + b + (d.length - h))
    mem.take l = d.take l ∧ mem.drop (l + b) = d.drop h := by
  intro D mem
  have hDl : D.length = l + b + (d.length - h) := hsize
  have hA : (D.take (l + b)).length = l + b := by simp only [List.length_take]; omega
  have hE : D.drop (l + b + (d.length - h)) = [] := List.drop_of_length_le (by omega)
  have hB : (D.drop h).take (d.length - h) = d.drop h := by
    have e : D.drop h = d.drop h ++ pad := List.drop_append_of_le_length hh
    rw [e]
    exact List.take_left' (by simp)
  have hM : mem = D.take (l + b) ++ d.drop h := by
    simp only [mem, hB, hE, List.append_nil]
  rw [hM]
  constructor
  · rw [List.take_append_of_le_length (by omega), List.take_take]
    have e2 : min l (l + b) = l := by omega
    rw [e2]
    exact List.take_append_of_le_length (by omega)
  · exact List.drop_left' hA

theorem resizeNoSize_data (b r : BA) (n : Int) (h : baResizeNoSize b n = .ok r) : r.data = b.data := by
  unfold baResizeNoSize at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  by_cases hx : b.exports > 0
  · simp [canResize, hx] at h
  have hc : canResize b = .ok () := by simp [canResize, hx]
  rw [hc] at h
  simp only at h
  cases hA : baResizeAlloc b n with
  | error e => rw [hA] at h; simp at h
  | ok p =>
    rw [hA] at h
    simp only [Except.ok.injEq] at h
    rw [← h]

theorem baCopyIn_data (self : BA) (l : Nat) (bytes : List Int) :
    (baCopyIn self l bytes).data =
      self.data.take l ++ bytes ++ self.data.drop (l + bytes.length) := by
  simp only [baCopyIn, Int.toNat_natCast]
  have e : ((l : Int) + (bytes.length : Int)).toNat = l + bytes.length := by omega
  rw [e]

theorem memmove_ok (mem : List Int) (dst src cnt : Nat) (h1 : dst + cnt ≤ mem.length)
    (h2 : src + cnt ≤ mem.length) :
    Sequences.memmove mem dst src cnt =
      .ok (mem.take dst ++ (mem.drop src).take cnt ++ mem.drop (dst + cnt)) := by
  have hc : (0 : Int) ≤ dst ∧ (0 : Int) ≤ src ∧ (0 : Int) ≤ cnt ∧ (dst : Int) + cnt ≤ mem.length ∧
      (src : Int) + cnt ≤ mem.length := by omega
  unfold Sequences.memmove
  rw [if_pos hc]
  have e : ((dst : Int) + cnt).toNat = dst + cnt := by omega
  simp [e]

/-- `bytearray_setslice_linear`: for every object and every valid range, a successful
splice leaves `data[:lo] + bytes + data[hi:]`, through all three branches (shrink by moving
`ob_start`, shrink by `memmove`, grow by `memmove`). -/
def SetsliceSpec : Prop :=
  ∀ (self r : BA) (lo hi : Nat) (bytes : List Int), lo ≤ hi → hi ≤ self.data.length →
    baSetsliceLinear self lo hi bytes = .ok r →
    r.data = self.data.take lo ++ bytes ++ self.data.drop hi

theorem setsliceSpec_proven : SetsliceSpec := by
  intro self r lo hi bytes hl hh h
  unfold baSetsliceLinear at h
  simp only at h
  have hsize : self.size = (self.data.length : Int) := rfl
  by_cases hneg : (bytes.length : Int) - ((hi : Int) - lo) < 0
  · rw [if_pos hneg] at h
    split at h
    · simp at h
    by_cases h0 : (lo : Int) = 0
    · rw [if_pos h0] at h
      have hlo : lo = 0 := by omega
      unfold baShrinkStart at h
      simp only [bind, Except.bind, pure, Except.pure] at h
      split at h
      · simp at h
      rename_i r' hr
      simp only [Except.ok.injEq] at h
      subst h
      have hd := resizeNoSize_data _ _ _ hr
      have e : (baCopyIn r' (0 : Int) bytes).data = _ := baCopyIn_data r' 0 bytes
      rw [e, hd, hlo]
      simp only [List.take_zero, List.nil_append, Nat.zero_add, List.drop_drop]
      congr 2
      omega
    · rw [if_neg h0] at h
      unfold baShrinkMove setsliceShrinkMove baMove at h
      have hM : Sequences.memmove self.data ((lo : Int) + bytes.length) hi (self.size - hi) =
          .ok (self.data.take (lo + bytes.length) ++ (self.data.drop hi).take (self.data.length - hi) ++
            self.data.drop (lo + bytes.length + (self.data.length - hi))) := by
        have e1 : (lo : Int) + bytes.length = ((lo + bytes.length : Nat) : Int) := by omega
        have e2 : self.size - hi = ((self.data.length - hi : Nat) : Int) := by rw [hsize]; omega
        rw [e1, e2]
        exact memmove_ok _ _ _ _ (by omega) (by omega)
      simp only [bind, Except.bind, pure, Except.pure, hM] at h
      split at h
      · simp at h
      rename_i r' hr
      simp only [Except.ok.injEq] at h
      subst h
      generalize hmem : self.data.take (lo + bytes.length) ++ (self.data.drop hi).take (self.data.length - hi) ++
            self.data.drop (lo + bytes.length + (self.data.length - hi)) = mem at hr
      have hlen : mem.length = self.data.length := by
        rw [← hmem]
        simp only [List.length_append, List.length_take, List.length_drop]
        omega
      obtain ⟨_, hc⟩ := baResize_cases _ _ _ hr
      rcases hc with ⟨_, he⟩ | ⟨_, _, hd, _, _⟩
      · simp only [BA.size] at he
        omega
      · have e := baCopyIn_data r' lo bytes
        have hT : (self.size + ((bytes.length : Int) - ((hi : Int) - lo))).toNat =
            lo + bytes.length + (self.data.length - hi) := by rw [hsize]; omega
        have hR : r'.data = mem.take (lo + bytes.length + (self.data.length - hi)) := by
          rw [hd]
          simp only [resizedData, hT]
          have : lo + bytes.length + (self.data.length - hi) - mem.length = 0 := by omega
          simp [this]
        obtain ⟨h1, h2⟩ := shrink_lists self.data lo bytes.length hi (by omega) hh
        rw [e, hR, ← hmem]
        rw [h1, h2]
  · rw [if_neg hneg] at h
    by_cases hpos : (bytes.length : Int) - ((hi : Int) - lo) > 0
    · rw [if_pos hpos] at h
      unfold baGrow baMove at h
      simp only [bind, Except.bind, pure, Except.pure] at h
      split at h
      · simp at h
      split at h
      · simp at h
      rename_i r' hr
      obtain ⟨_, hc⟩ := baResize_cases _ _ _ hr
      rcases hc with ⟨_, he⟩ | ⟨_, _, hd, _, _⟩
      · omega
      have hT : (self.size + ((bytes.length : Int) - ((hi : Int) - lo))).toNat =
          lo + bytes.length + (self.data.length - hi) := by rw [hsize]; omega
      have hRl : r'.data = self.data ++ List.replicate (lo + bytes.length + (self.data.length - hi) - self.data.length) uninit := by
        rw [hd]
        simp only [resizedData, hT]
        rw [List.take_of_length_le (by omega)]
      have hLen : (self.data ++ List.replicate (lo + bytes.length + (self.data.length - hi) - self.data.length) uninit).length
          = lo + bytes.length + (self.data.length - hi) := by
        simp only [List.length_append, List.length_replicate]
        omega
      have hSz : r'.size = ((lo + bytes.length + (self.data.length - hi) : Nat) : Int) := by
        simp only [BA.size, hRl, hLen]
      have hM : Sequences.memmove r'.data ((lo : Int) + bytes.length) hi (r'.size - lo - bytes.length) =
          .ok (r'.data.take (lo + bytes.length) ++ (r'.data.drop hi).take (self.data.length - hi) ++
            r'.data.drop (lo + bytes.length + (self.data.length - hi))) := by
        have e1 : (lo : Int) + bytes.length = ((lo + bytes.length : Nat) : Int) := by omega
        have e2 : r'.size - lo - bytes.length = ((self.data.length - hi : Nat) : Int) := by rw [hSz]; omega
        rw [e1, e2]
        have hl2 : r'.data.length = lo + bytes.length + (self.data.length - hi) := by rw [hRl, hLen]
        exact memmove_ok _ _ _ _ (by omega) (by omega)
      obtain ⟨mem, hmem⟩ : ∃ mem, mem = r'.data.take (lo + bytes.length) ++
          (r'.data.drop hi).take (self.data.length - hi) ++
          r'.data.drop (lo + bytes.length + (self.data.length - hi)) := ⟨_, rfl⟩
      rw [← hmem] at hM
      rw [hM] at h
      simp only [Except.ok.injEq] at h
      subst h
      have e := baCopyIn_data { r' with data := mem } lo bytes
      rw [e]
      obtain ⟨h1, h2⟩ := grow_lists self.data _ lo bytes.length hi hh hl hLen
      simp only
      rw [hRl] at hmem
      rw [hmem, h1, h2]
    · rw [if_neg hpos] at h
      simp only [Except.ok.injEq] at h
      subst h
      rw [baCopyIn_data]
      have : lo + bytes.length = hi := by omega
      rw [this]

theorem extendInitialised_proven : ExtendInitialised := by
  refine ⟨?_, by decide⟩
  intro self m r v mutate hm h
  unfold baExtendBuffer baSetslice at h
  simp only [bind, Except.bind, pure, Except.pure, hm] at h
  have hs : self.size = (self.data.length : Int) := rfl
  have hm2 : m.size = (m.data.length : Int) := rfl
  have h1 : ¬ (self.size < 0) := by omega
  rw [if_neg h1] at h
  dsimp only
  by_cases hc : self.size > m.size
  · rw [if_pos hc] at h
    have h2 : ¬ (self.size < m.size) := by omega
    rw [if_neg h2, if_pos hc] at h
    have e : (min self.size m.size).toNat = m.data.length := by omega
    rw [e, hm2] at *
    exact setsliceSpec_proven m r m.data.length m.data.length _ (by omega) (by omega) h
  · rw [if_neg hc] at h
    have h2 : ¬ (self.size < self.size) := by omega
    rw [if_neg h2, if_neg hc] at h
    have e : (min self.size m.size).toNat = self.data.length := by omega
    rw [e, hs] at *
    exact setsliceSpec_proven m r self.data.length self.data.length _ (by omega) (by omega) h

end PyLean.BytesObj.Bytes
