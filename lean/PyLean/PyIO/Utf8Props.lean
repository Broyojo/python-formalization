import PyLean.PyIO.Text

/-!
UTF-8 facts used by the `StringIO` proofs: decoding (with `surrogatepass`)
inverts encoding, and encoding a string without NUL produces no zero byte.
-/

namespace PyLean.PyIO

open PyLean

theorem utf8Enc_cons (c : Nat) (r : List Nat) : utf8Enc (c :: r) = utf8Enc1 c ++ utf8Enc r := by
  simp [utf8Enc, List.flatMap_cons]

theorem utf8Enc_nil : utf8Enc [] = [] := rfl

theorem utf8Enc1_ne_nil (c : Nat) : utf8Enc1 c ≠ [] := by
  unfold utf8Enc1; split <;> (try split) <;> (try split) <;> simp

theorem utf8Dec1_enc (c : Nat) (hc : c < 0x110000) (rest : List Nat) :
    utf8Dec1 (utf8Enc1 c ++ rest) = .char c (utf8Enc1 c).length := by
  unfold utf8Enc1
  by_cases h1 : c < 0x80
  · simp only [h1, ite_true, List.singleton_append, List.length_singleton]
    simp [utf8Dec1, seqLen, h1]
  · simp only [h1, ite_false]
    by_cases h2 : c < 0x800
    · simp only [h2, ite_true]
      have l1 : ¬ (0xC0 + c / 64 < 0x80) := by omega
      have l2 : 0xC2 ≤ 0xC0 + c / 64 ∧ 0xC0 + c / 64 ≤ 0xDF := by omega
      simp only [utf8Dec1, seqLen, l1, l2, ite_false, ite_true, List.cons_append, List.nil_append]
      have e1 : ¬ (0xC0 + c / 64 = 0xE0) := by omega
      have e2 : ¬ (0xC0 + c / 64 = 0xF0) := by omega
      have e3 : ¬ (0xC0 + c / 64 = 0xF4) := by omega
      have k : isCont (0x80 + c % 64) = true := by simp [isCont]; omega
      simp [secondOk, e1, e2, e3, k]
      all_goals (repeat' split)
      all_goals first | (congr 1 <;> omega) | (exfalso; omega)
    · simp only [h2, ite_false]
      by_cases h3 : c < 0x10000
      · simp only [h3, ite_true]
        have l1 : ¬ (0xE0 + c / 4096 < 0x80) := by omega
        have l2 : ¬ (0xC2 ≤ 0xE0 + c / 4096 ∧ 0xE0 + c / 4096 ≤ 0xDF) := by omega
        have l3 : 0xE0 ≤ 0xE0 + c / 4096 ∧ 0xE0 + c / 4096 ≤ 0xEF := by omega
        simp only [utf8Dec1, seqLen, l1, l2, l3, ite_false, ite_true, List.cons_append, List.nil_append]
        have e2 : ¬ (0xE0 + c / 4096 = 0xF0) := by omega
        have e3 : ¬ (0xE0 + c / 4096 = 0xF4) := by omega
        have k2 : isCont (0x80 + c / 64 % 64) = true := by simp [isCont]; omega
        have k3 : isCont (0x80 + c % 64) = true := by simp [isCont]; omega
        by_cases e1 : 0xE0 + c / 4096 = 0xE0
        · have s : (0xA0 ≤ 0x80 + c / 64 % 64 && 0x80 + c / 64 % 64 ≤ 0xBF) = true := by
            simp; omega
          simp [secondOk, e1, s, k3]
          all_goals (repeat' split)
          all_goals first | (congr 1 <;> omega) | (exfalso; omega)
        · simp [secondOk, e1, e2, e3, k2, k3]
          all_goals (repeat' split)
          all_goals first | (congr 1 <;> omega) | (exfalso; omega)
      · simp only [h3, ite_false]
        have l1 : ¬ (0xF0 + c / 262144 < 0x80) := by omega
        have l2 : ¬ (0xC2 ≤ 0xF0 + c / 262144 ∧ 0xF0 + c / 262144 ≤ 0xDF) := by omega
        have l3 : ¬ (0xE0 ≤ 0xF0 + c / 262144 ∧ 0xF0 + c / 262144 ≤ 0xEF) := by omega
        have l4 : 0xF0 ≤ 0xF0 + c / 262144 ∧ 0xF0 + c / 262144 ≤ 0xF4 := by omega
        simp only [utf8Dec1, seqLen, l1, l2, l3, l4, ite_false, ite_true, List.cons_append, List.nil_append]
        have e1 : ¬ (0xF0 + c / 262144 = 0xE0) := by omega
        have k3 : isCont (0x80 + c / 64 % 64) = true := by simp [isCont]; omega
        have k4 : isCont (0x80 + c % 64) = true := by simp [isCont]; omega
        by_cases f0 : 0xF0 + c / 262144 = 0xF0
        · have s : (0x90 ≤ 0x80 + c / 4096 % 64 && 0x80 + c / 4096 % 64 ≤ 0xBF) = true := by
            simp; omega
          simp [secondOk, e1, f0, s, k3, k4]
          all_goals (repeat' split)
          all_goals first | (congr 1 <;> omega) | (exfalso; omega)
        · by_cases f4 : 0xF0 + c / 262144 = 0xF4
          · have s : (0x80 ≤ 0x80 + c / 4096 % 64 && 0x80 + c / 4096 % 64 ≤ 0x8F) = true := by
              simp; omega
            simp [secondOk, e1, f0, f4, s, k3, k4]
            all_goals (repeat' split)
            all_goals first | (congr 1 <;> omega) | (exfalso; omega)
          · have k2 : isCont (0x80 + c / 4096 % 64) = true := by simp [isCont]; omega
            simp [secondOk, e1, f0, f4, k2, k3, k4]
            all_goals (repeat' split)
            all_goals first | (congr 1 <;> omega) | (exfalso; omega)

/-- Valid code points (the type invariant of `str`). -/
def ValidStr (s : List Nat) : Prop := ∀ c ∈ s, c < 0x110000

theorem utf8DecF_enc (final : Bool) : ∀ (s : List Nat) (fuel : Nat), ValidStr s →
    (utf8Enc s).length < fuel → utf8DecF final fuel (utf8Enc s) = .ok (s, []) := by
  intro s
  induction s with
  | nil =>
    intro fuel _ hf
    cases fuel with
    | zero => simp at hf
    | succ f => simp [utf8Enc_nil, utf8DecF]
  | cons c r ih =>
    intro fuel hv hf
    have hc : c < 0x110000 := hv c (List.mem_cons_self ..)
    have hr : ValidStr r := fun x hx => hv x (List.mem_cons_of_mem _ hx)
    cases fuel with
    | zero => simp at hf
    | succ f =>
      rw [utf8Enc_cons] at hf ⊢
      obtain ⟨x, xs, hxs⟩ : ∃ x xs, utf8Enc1 c ++ utf8Enc r = x :: xs := by
        cases h : utf8Enc1 c ++ utf8Enc r with
        | nil => exact absurd (List.append_eq_nil_iff.mp h).1 (utf8Enc1_ne_nil c)
        | cons x xs => exact ⟨x, xs, rfl⟩
      rw [hxs]
      simp only [utf8DecF]
      rw [← hxs, utf8Dec1_enc c hc]
      simp only [List.drop_left]
      have hpos : 0 < (utf8Enc1 c).length := List.length_pos_iff.mpr (utf8Enc1_ne_nil c)
      rw [ih f hr (by simp at hf; omega)]

theorem utf8Dec_enc (final : Bool) (s : List Nat) (hv : ValidStr s) :
    utf8Dec final (utf8Enc s) = .ok (s, []) :=
  utf8DecF_enc final s _ hv (Nat.lt_succ_self _)

theorem utf8Enc1_nonzero (c : Nat) (hc : c ≠ 0) : ∀ b ∈ utf8Enc1 c, b ≠ 0 := by
  unfold utf8Enc1
  split
  · simp; omega
  · split
    · simp
    · split <;> simp

theorem utf8Enc_nonzero (s : List Nat) (hs : ∀ c ∈ s, c ≠ 0) : ∀ b ∈ utf8Enc s, b ≠ 0 := by
  induction s with
  | nil => simp [utf8Enc_nil]
  | cons c r ih =>
    rw [utf8Enc_cons]
    intro b hb
    rcases List.mem_append.mp hb with h | h
    · exact utf8Enc1_nonzero c (hs c (List.mem_cons_self ..)) b h
    · exact ih (fun x hx => hs x (List.mem_cons_of_mem _ hx)) b h

/-- The UTF-8 encoding is `[]`, `[10]`, `[13]` or `[13, 10]` exactly for the
same code-point strings. -/
theorem utf8Enc_small (s : List Nat) (hv : ValidStr s) (t : List Nat) (ht : t.all (· < 0x80) = true) :
    utf8Enc s = t ↔ s = t := by
  induction s generalizing t with
  | nil =>
    simp only [utf8Enc_nil]
  | cons c r ih =>
    have hc : c < 0x110000 := hv c (List.mem_cons_self ..)
    have hr : ValidStr r := fun x hx => hv x (List.mem_cons_of_mem _ hx)
    rw [utf8Enc_cons]
    cases t with
    | nil =>
      constructor
      · intro h; exact absurd (List.append_eq_nil_iff.mp h).1 (utf8Enc1_ne_nil c)
      · intro h; cases h
    | cons x xs =>
      simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at ht
      by_cases h1 : c < 0x80
      · have e : utf8Enc1 c = [c] := by simp [utf8Enc1, h1]
        rw [e, List.singleton_append, List.cons.injEq, List.cons.injEq, ih hr xs ht.2]
      · constructor
        · intro h
          have hx : (utf8Enc1 c ++ utf8Enc r).head? = some x := by rw [h]; rfl
          unfold utf8Enc1 at hx
          simp only [h1, ite_false] at hx
          split at hx <;> (try split at hx) <;> simp at hx <;> omega
        · intro h; cases h; omega

end PyLean.PyIO
