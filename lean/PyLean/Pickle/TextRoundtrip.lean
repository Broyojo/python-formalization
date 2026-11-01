import PyLean.Pickle.IntNarrow

/-!
The protocol 0/1 text encodings round trip: the lines `save_long` writes are
read back as the same int by both unpicklers.
-/

namespace PyLean.Pickle

open PyLean

theorem digitsVal_snoc (l : List Nat) (d : Nat) : digitsVal (l ++ [d]) = 10 * digitsVal l + d := by
  simp [digitsVal, List.foldl_append]

theorem digit_byte (d : Nat) (h : d < 10) : isDigit (48 + d).toUInt8 = true ∧
    (48 + d).toUInt8.toNat - 48 = d := by
  have e : (48 + d).toUInt8.toNat = 48 + d := by simp; omega
  constructor
  · simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · apply UInt8.le_iff_toNat_le.mpr; rw [e]; simp <;> omega
    · apply UInt8.le_iff_toNat_le.mpr; rw [e]; simp <;> omega
  · omega

theorem decDigits_spec (n : Nat) : decDigits n ≠ [] ∧ (∀ c ∈ decDigits n, isDigit c = true) ∧
    digitsVal ((decDigits n).map (fun c => c.toNat - 48)) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [decDigits]
    split
    · rename_i h
      have := digit_byte n h
      refine ⟨by simp, ?_, ?_⟩
      · intro c hc; rw [List.mem_singleton] at hc; subst hc; exact this.1
      · simp only [List.map_cons, List.map_nil]
        rw [this.2]
        simp [digitsVal]
    · rename_i h
      obtain ⟨h1, h2, h3⟩ := ih (n / 10) (by omega)
      have hd := digit_byte (n % 10) (by omega)
      refine ⟨by simp, ?_, ?_⟩
      · intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · exact h2 c hc
        · rw [List.mem_singleton] at hc; subst hc; exact hd.1
      · rw [List.map_append]
        simp only [List.map_cons, List.map_nil]
        rw [digitsVal_snoc, h3, hd.2]
        omega

theorem digit_not_space {c : UInt8} (h : isDigit c = true) : isSpace c = false := by
  cases hs : isSpace c with
  | false => rfl
  | true => have := isSpace_not_digit hs; rw [h] at this; simp at this

theorem digit_ne {c : UInt8} (h : isDigit c = true) : c ≠ 0 ∧ c ≠ nl ∧ c ≠ 0x2b ∧ c ≠ 0x2d ∧ c ≠ 0x4c := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (intro e; subst e; revert h; decide)

theorem pyLong_decDigits (n : Nat) (hlen : (decDigits n).length ≤ maxStrDigits) (neg : Bool) :
    lfsBase neg (decDigits n) = .ok (if neg then -(n : Int) else n) := by
  obtain ⟨h1, h2, h3⟩ := decDigits_spec n
  rw [lfsBase_digits neg _ h2 h1 hlen, h3]

theorem pyLong_dec (x : Int) (hlen : (decDigits x.natAbs).length ≤ maxStrDigits) :
    pyLongFromString (decInt x) = .ok x := by
  obtain ⟨h1, h2, _⟩ := decDigits_spec x.natAbs
  unfold pyLongFromString decInt
  by_cases hx : x < 0
  · rw [if_pos hx]
    have e : skipSpace ((0x2d : UInt8) :: decDigits x.natAbs) = 0x2d :: decDigits x.natAbs := by
      simp [skipSpace, isSpace]
    rw [e]
    show lfsBase true (decDigits x.natAbs) = _
    rw [pyLong_decDigits _ hlen true]
    simp only [↓reduceIte]
    congr 1
    omega
  · rw [if_neg hx]
    generalize hd : decDigits x.natAbs = ds at *
    cases ds with
    | nil => exact absurd rfl h1
    | cons a r =>
      have ha := h2 a List.mem_cons_self
      obtain ⟨_, _, h3, h4, _⟩ := digit_ne ha
      have e : skipSpace (a :: r) = a :: r := by simp [skipSpace, digit_not_space ha]
      have e2 : signSplit (a :: r) = (false, a :: r) := by
        unfold signSplit; split <;> rename_i heq
        · simp at heq; exact absurd heq.1 h3
        · simp at heq; exact absurd heq.1 h4
        · rfl
      rw [e, e2]
      show lfsBase false (a :: r) = _
      rw [← hd, pyLong_decDigits _ (by rw [hd]; exact hlen) false]
      simp only [Bool.false_eq_true, ↓reduceIte]
      congr 1
      omega

theorem dec_mem (x : Int) (c : UInt8) (h : c ∈ decInt x) : isDigit c = true ∨ c = 0x2d := by
  obtain ⟨_, h2, _⟩ := decDigits_spec x.natAbs
  unfold decInt at h
  split at h
  · rcases List.mem_cons.mp h with rfl | h
    · exact Or.inr rfl
    · exact Or.inl (h2 c h)
  · exact Or.inl (h2 c h)

theorem dec_no_nl (x : Int) : nl ∉ decInt x := by
  intro h
  rcases dec_mem x nl h with h | h
  · exact (digit_ne h).2.1 rfl
  · revert h; decide

theorem dec_no_zero (x : Int) : (0 : UInt8) ∉ decInt x := by
  intro h
  rcases dec_mem x 0 h with h | h
  · exact (digit_ne h).1 rfl
  · revert h; decide

theorem dec_filter (x : Int) : ((decInt x).filter isDigit).length ≤ (decDigits x.natAbs).length := by
  unfold decInt
  split
  · simp only [List.filter_cons]
    have : isDigit 0x2d = false := by decide
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    exact List.length_filter_le _ _
  · exact List.length_filter_le _ _

theorem pyInt_dec (x : Int) (hlen : (decDigits x.natAbs).length ≤ maxStrDigits) :
    pyIntOfBytes (decInt x) = .ok x := by
  unfold pyIntOfBytes
  dsimp only
  rw [takeWhile_ne_zero_of_not_mem (dec_no_zero x), pyLong_dec x hlen]
  simp

theorem pyInt_dec_nl (x : Int) (hlen : (decDigits x.natAbs).length ≤ maxStrDigits) :
    pyIntOfBytes (decInt x ++ [nl]) = .ok x := by
  have hz : (0 : UInt8) ∉ decInt x ++ [nl] := by
    simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨dec_no_zero x, by decide⟩
  unfold pyIntOfBytes
  dsimp only
  rw [takeWhile_ne_zero_of_not_mem hz, pyLongFromString_append_space _ isSpace_nl, pyLong_dec x hlen]
  simp

theorem dec_not_bool (x : Int) : ¬ BoolSpelling (decInt x) := by
  rintro ⟨a, d, hb, hd, ha⟩
  by_cases hx : x < 0
  · have h1 : decInt x = 0x2d :: decDigits x.natAbs := by unfold decInt; rw [if_pos hx]
    rw [h1] at hb
    simp only [List.cons.injEq] at hb
    obtain ⟨ha2, hds⟩ := hb
    obtain ⟨_, _, h3⟩ := decDigits_spec x.natAbs
    rw [hds] at h3
    have hd0 : d.toNat - 48 ≠ 0 := by
      intro h
      simp [digitsVal, h] at h3
      omega
    rcases hd with rfl | rfl
    · simp at hd0
    · rcases ha with h | h | ⟨_, h⟩
      · subst ha2; revert h; decide
      · subst ha2; revert h; decide
      · revert h; decide
  · have hneg : decInt x = decDigits x.natAbs := by unfold decInt; rw [if_neg hx]
    obtain ⟨_, h2, _⟩ := decDigits_spec x.natAbs
    have hdig : isDigit a = true := h2 a (by rw [← hneg, hb]; simp)
    obtain ⟨_, _, h3, h4, _⟩ := digit_ne hdig
    rcases ha with h | h | ⟨h, _⟩
    · rw [digit_not_space hdig] at h; simp at h
    · exact h3 h
    · exact h4 h

/-- For every int with at most 4300 decimal digits (beyond which `repr` raises),
the lines `save_long` writes for protocols 0 and 1, `I<x>` and `L<x>L`, read
back as the int `x` in both unpicklers. -/
def TextIntRoundtrip : Prop :=
  ∀ x : Int, (decDigits x.natAbs).length ≤ maxStrDigits →
    pyLoadIntLine (decInt x ++ [nl]) = .ok (.int x) ∧ cLoadIntLine (decInt x ++ [nl]) = .ok (.int x) ∧
    pyLoadLongLine (decInt x ++ [0x4c, nl]) = .ok x ∧ cLoadLongLine (decInt x ++ [0x4c, nl]) = .ok x

theorem textIntRoundtrip_proven : TextIntRoundtrip := by
  intro x hlen
  have h0 : ¬ decInt x ++ [nl] = [0x30, 0x30, nl] := by
    intro h
    have e : decInt x = [0x30, 0x30] := by
      have h' : decInt x ++ [nl] = [0x30, 0x30] ++ [nl] := h
      exact (List.append_inj' h' rfl).1
    have h1 := pyLong_dec x hlen
    rw [e] at h1
    have h2 : pyLongFromString [0x30, 0x30] = .ok 0 := by decide +kernel
    rw [h2] at h1
    have hx : x = 0 := by simpa using h1.symm
    subst hx
    revert e
    decide +kernel
  have h1 : ¬ decInt x ++ [nl] = [0x30, 0x31, nl] := by
    intro h
    have e : decInt x = [0x30, 0x31] := by
      have h' : decInt x ++ [nl] = [0x30, 0x31] ++ [nl] := h
      exact (List.append_inj' h' rfl).1
    have h1 := pyLong_dec x hlen
    rw [e] at h1
    have h2 : pyLongFromString [0x30, 0x31] = .ok 1 := by decide +kernel
    rw [h2] at h1
    have hx : x = 1 := by simpa using h1.symm
    subst hx
    revert e
    decide +kernel
  have hpy : pyLoadIntLine (decInt x ++ [nl]) = .ok (.int x) := by
    unfold pyLoadIntLine
    rw [if_neg h0, if_neg h1, pyInt_dec_nl x hlen]
    rfl
  have hlong : pyLoadLongLine (decInt x ++ [0x4c, nl]) = .ok x := by
    unfold pyLoadLongLine
    have e1 : (decInt x ++ [0x4c, nl]).dropLast = decInt x ++ [0x4c] := by
      rw [show decInt x ++ [(0x4c : UInt8), nl] = (decInt x ++ [0x4c]) ++ [nl] by simp]
      simp
    rw [e1]
    dsimp only
    rw [if_pos ⟨by simp, by simp⟩]
    simp only [List.dropLast_concat]
    exact pyInt_dec x hlen
  refine ⟨hpy, ?_, hlong, ?_⟩
  · have := intLineTwinsNarrow_proven (decInt x) (dec_no_nl x) (dec_no_zero x) (dec_not_bool x)
      (Nat.le_trans (dec_filter x) hlen)
    rw [hpy] at this
    cases hc : cLoadIntLine (decInt x ++ [nl]) with
    | error e => rw [hc] at this; exact this.elim
    | ok v => rw [hc] at this; rw [show v = .int x from this]
  · have hbody : nl ∉ decInt x ++ [0x4c] := by
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨dec_no_nl x, by decide⟩
    have hz : (0 : UInt8) ∉ decInt x ++ [0x4c] := by
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨dec_no_zero x, by decide⟩
    have := longLineTwinsNoNul_proven _ hbody hz
    rw [show (decInt x ++ [(0x4c : UInt8)]) ++ [nl] = decInt x ++ [0x4c, nl] by simp, hlong] at this
    cases hc : cLoadLongLine (decInt x ++ [0x4c, nl]) with
    | error e => rw [hc] at this; exact this.elim
    | ok v => rw [hc] at this; rw [show v = x from this]

end PyLean.Pickle
