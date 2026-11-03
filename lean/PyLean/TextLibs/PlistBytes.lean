import PyLean.TextLibs.PlistTotal
import PyLean.TextLibs.PlistWrite

/-! Byte-level lemmas for the round trip: big-endian integers, and what the reader's file
operations return on a buffer whose bytes are known. -/

namespace PyLean.TextLibs.Plist

open PyLean PyLean.TextLibs

theorem beVal_append (l : List Nat) (a : Nat) : beVal (l ++ [a]) = beVal l * 256 + a := by
  simp [beVal, List.foldl_append]

theorem beBytes_length (n k : Nat) : (beBytes n k).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [beBytes, ih]

theorem beBytes_lt (n k : Nat) : ∀ b ∈ beBytes n k, b < 256 := by
  induction k generalizing n with
  | zero => simp [beBytes]
  | succ k ih =>
    intro b hb
    simp only [beBytes, List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | rfl
    · exact ih _ b hb
    · omega

theorem beVal_beBytes (k : Nat) : ∀ n, n < 256 ^ k → beVal (beBytes n k) = n := by
  induction k with
  | zero => intro n h; simp at h; subst h; rfl
  | succ k ih =>
    intro n h
    simp only [beBytes, beVal_append]
    rw [Nat.pow_succ] at h
    rw [ih (n / 256) (by omega)]
    omega

theorem chunks_packRefs (size : Nat) (hs : 1 ≤ size) :
    ∀ (xs : List Nat), (∀ x ∈ xs, x < 256 ^ size) →
      (chunks size xs.length (packRefs size xs)).map beVal = xs
  | [] , _ => rfl
  | x :: xs, h => by
    simp only [packRefs, List.flatMap_cons, List.length_cons, chunks, List.map_cons]
    have hl := beBytes_length x size
    rw [List.take_left' hl, List.drop_left' hl]
    rw [beVal_beBytes size x (h x (by simp))]
    have := chunks_packRefs size hs xs (fun y hy => h y (by simp [hy]))
    simp only [packRefs] at this
    rw [this]

theorem packRefs_length (size : Nat) (xs : List Nat) : (packRefs size xs).length = size * xs.length := by
  induction xs with
  | nil => simp [packRefs]
  | cons x xs ih =>
    simp only [packRefs, List.flatMap_cons, List.length_append, beBytes_length] at ih ⊢
    rw [ih, List.length_cons, Nat.mul_succ]
    omega

/-! ## Reading known bytes -/

theorem read_prefix (B : List Nat) (p : Nat) (d rest : List Nat) (h : B.drop p = d ++ rest) :
    FP.read ⟨B, p⟩ d.length = (d, ⟨B, p + d.length⟩) := by
  have hl : B.length - p = d.length + rest.length := by
    rw [← List.length_drop, h, List.length_append]
  simp only [FP.read, hl, h]
  rw [Nat.min_eq_left (by omega), List.take_left' rfl]

theorem read_take (B : List Nat) (p k : Nat) (d rest : List Nat) (h : B.drop p = d ++ rest)
    (hk : k ≤ d.length) : FP.read ⟨B, p⟩ k = (d.take k, ⟨B, p + k⟩) := by
  have hl : B.length - p = d.length + rest.length := by
    rw [← List.length_drop, h, List.length_append]
  simp only [FP.read, hl, h]
  rw [Nat.min_eq_left (by omega), List.take_append_of_le_length hk]

theorem readLoop_prefix (r : Nat) (hr : 1 ≤ r) (B : List Nat) (p : Nat) (d rest : List Nat)
    (h : B.drop p = d ++ rest) :
    ∀ fuel cursize, cursize ≤ d.length → (cursize = 0 → d.length = 0) → d.length - cursize < fuel →
      readLoop r d.length fuel ⟨B, p + cursize⟩ cursize (d.take cursize) = .ok (d, ⟨B, p + d.length⟩)
  | 0, _, _, _, hf => by omega
  | fuel + 1, cursize, h1, h0, hf => by
    unfold readLoop
    have hlen : (d.take cursize).length = cursize := by simp; omega
    rw [if_neg (by omega)]
    by_cases he : cursize = d.length
    · rw [if_pos he]
      subst he
      simp
    · rw [if_neg he]
      have hc : 0 < cursize := by
        rcases Nat.eq_zero_or_pos cursize with hz | hz
        · exact absurd (hz.trans (h0 hz).symm) he
        · exact hz
      have hdrop : B.drop (p + cursize) = d.drop cursize ++ rest := by
        rw [← List.drop_drop, h, List.drop_append_of_le_length h1]
      have hdel : min cursize (d.length - cursize) ≤ (d.drop cursize).length := by
        simp; omega
      dsimp only
      rw [read_take B (p + cursize) _ (d.drop cursize) rest hdrop hdel]
      dsimp only
      have e1 : d.take cursize ++ (d.drop cursize).take (min cursize (d.length - cursize)) =
          d.take (cursize + min cursize (d.length - cursize)) := by
        rw [List.take_add]
      rw [e1, Nat.add_assoc]
      exact readLoop_prefix r hr B p d rest h fuel _ (by omega) (by omega) (by omega)

theorem readR_prefix (r : Nat) (hr : 2 ≤ r) (B : List Nat) (p : Nat) (d rest : List Nat)
    (h : B.drop p = d ++ rest) : readR r ⟨B, p⟩ d.length = .ok (d, ⟨B, p + d.length⟩) := by
  obtain ⟨r, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
  simp only [readR, call]
  have hk : min d.length minReadBuf ≤ d.length := Nat.min_le_left _ _
  rw [read_take B p _ d rest h hk]
  dsimp only
  exact readLoop_prefix r (by omega) B p d rest h _ _ hk
    (by intro hz; have : minReadBuf = 2 ^ 20 := rfl; omega) (by omega)

end PyLean.TextLibs.Plist
