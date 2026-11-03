import PyLean.TextLibs.PlistKeys

/-! The binary round trip: what `dumps(value, fmt=FMT_BINARY)` writes, `loads` reads back as the
same object graph. -/

namespace PyLean.TextLibs.Plist

open PyLean PyLean.TextLibs

theorem call_ok' {α : Type} {r : Nat} {f : Nat → Py α} {y : α} (h : call r f = .ok y) :
    ∃ k, r = k + 1 ∧ f k = .ok y := by
  cases r with
  | zero => simp [call] at h
  | succ k => exact ⟨k, rfl, h⟩

theorem dumps_binary (xmlw : XmlWrite) (r : Nat) (H : WHeap) (root : Nat) (cfg : WCfg) (b : List Nat)
    (h : dumpsR xmlw r H root .binary cfg = .ok b) : ∃ k, binaryWriteR k H cfg root = .ok b := by
  obtain ⟨k1, _, h1⟩ := call_ok' h
  obtain ⟨k2, _, h2⟩ := call_ok' h1
  simp only [bind, Except.bind] at h2
  cases k2 with
  | zero => simp [call] at h2
  | succ k3 => exact ⟨k3 + 1, by simpa [call] using h2⟩

theorem countToSize_cases (n : Nat) : (n < 2 ^ 8 ∧ countToSize n = 1) ∨
    (n < 2 ^ 16 ∧ countToSize n = 2) ∨ (n < 2 ^ 32 ∧ countToSize n = 4) ∨ countToSize n = 8 := by
  unfold countToSize
  by_cases h1 : n < 2 ^ 8
  · rw [if_pos h1]; exact Or.inl ⟨h1, rfl⟩
  · rw [if_neg h1]
    by_cases h2 : n < 2 ^ 16
    · rw [if_pos h2]; exact Or.inr (Or.inl ⟨h2, rfl⟩)
    · rw [if_neg h2]
      by_cases h3 : n < 2 ^ 32
      · rw [if_pos h3]; exact Or.inr (Or.inr (Or.inl ⟨h3, rfl⟩))
      · rw [if_neg h3]; exact Or.inr (Or.inr (Or.inr rfl))

theorem countToSize_bin (n : Nat) : binaryFormat (countToSize n) = true := by
  rcases countToSize_cases n with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | h <;> rw [h] <;> rfl

theorem countToSize_lt (n : Nat) (h : n < 2 ^ 64) : n < 256 ^ countToSize n := by
  rcases countToSize_cases n with ⟨h1, e⟩ | ⟨h1, e⟩ | ⟨h1, e⟩ | e <;> rw [e] <;> simp <;> omega

theorem countToSize_pos (n : Nat) : 1 ≤ countToSize n := by
  rcases countToSize_cases n with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | h <;> rw [h] <;> decide

/-- The written file: header, objects, offset table, trailer. -/
structure Written (H : WHeap) (cfg : WCfg) (root : Nat) (b : List Nat) where
  st : WState
  k : Nat
  offsets : List Nat
  body : List Nat
  top : Nat
  hflat : flattenR H cfg k root WState.init = .ok st
  hall : writeAll k H cfg (countToSize st.objlist.length) st st.objlist
    (List.replicate st.objlist.length 0) [] = .ok (offsets, body)
  htop : lookupW H st root = some top
  hb : b = bplistHeader ++ body ++ packRefs (countToSize (8 + body.length)) offsets ++
    ([0, 0, 0, 0, 0, 0, countToSize (8 + body.length), countToSize st.objlist.length] ++
      beBytes st.objlist.length 8 ++ beBytes top 8 ++ beBytes (8 + body.length) 8)

theorem written_of (H : WHeap) (cfg : WCfg) (root : Nat) (b : List Nat) (k : Nat)
    (h : binaryWriteR k H cfg root = .ok b) : Nonempty (Written H cfg root b) := by
  obtain ⟨k, _, h⟩ := call_ok' h
  simp only [bind, Except.bind] at h
  cases hf : flattenR H cfg k root WState.init with
  | error e => rw [hf] at h; cases h
  | ok st =>
  rw [hf] at h
  simp only at h
  cases hc : countToSizeR k st.objlist.length with
  | error e => rw [hc] at h; cases h
  | ok rs =>
  rw [hc] at h
  simp only at h
  have hrs : rs = countToSize st.objlist.length := (call_ok hc)
  subst hrs
  cases hw : writeAll k H cfg (countToSize st.objlist.length) st st.objlist
      (List.replicate st.objlist.length 0) [] with
  | error e => rw [hw] at h; cases h
  | ok p =>
  rcases p with ⟨offsets, body⟩
  rw [hw] at h
  simp only at h
  cases hg : getrefnumR k H st root with
  | error e => rw [hg] at h; cases h
  | ok top =>
  rw [hg] at h
  simp only at h
  cases hc2 : countToSizeR k (8 + body.length) with
  | error e => rw [hc2] at h; cases h
  | ok os =>
  rw [hc2] at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  have hos : os = countToSize (8 + body.length) := call_ok hc2
  subst hos
  exact ⟨⟨st, k, offsets, body, top, hf, hw, getrefnumR_ok k H st root top hg, by rw [← h]⟩⟩

end PyLean.TextLibs.Plist
