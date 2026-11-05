import PyLean.TextLibs.BinasciiB85e

/-!
The group refusals of `binascii.a2b_base85`: "Base85 overflow in hunk starting at byte N" and
"Incomplete Base85 group", exactly, for every input of alphabet characters.
-/

namespace PyLean.TextLibs.Binascii

open PyLean

set_option linter.unusedSimpArgs false

/-- The values of the groups of five digits, the last one padded with the largest digit as the decoder
does. -/
def groups85 : List Nat → List Nat
  | v0 :: v1 :: v2 :: v3 :: v4 :: r => val85 [v0, v1, v2, v3, v4] :: groups85 r
  | [] => []
  | short => [val85 (short ++ List.replicate (5 - short.length) 84)]

/-- The index of the first group that does not fit in 32 bits. -/
def firstOver : List Nat → Option Nat
  | [] => none
  | g :: gs => if g ≥ 2 ^ 32 then some 0 else (firstOver gs).map (· + 1)

def ovf85 (j : Nat) : String := s!"Base85 overflow in hunk starting at byte {j}"

theorem ovf85_ne (j : Nat) (m : String) (hm : m.length < 41) : ovf85 j ≠ m := by
  intro h
  have := congrArg String.length h
  simp only [ovf85] at this
  rw [String.length_append] at this
  have : (toString "Base85 overflow in hunk starting at byte ").length = 41 := by decide
  omega

/-- The fifth digit of a group that overflows. -/
theorem b85_ov5 (t : Nat → Nat) (ig : Option (List Nat)) (k : Bool) (N f c l : Nat) (o r : List Nat) (len : Int)
    (hd : t c < 85) (hlen : 0 < len) (hov : l * 85 + t c ≥ 2 ^ 32) :
    a2bB85Loop t ig k N (f + 1) (c :: r) len ⟨l, 4, o⟩ =
      .error (err s!"Base85 overflow in hunk starting at byte {(((N : Int) - len).toNat) / 5 * 5}") := by
  have h1 : decide (len ≤ 0) = false := by simp; omega
  simp only [a2bB85Loop, h1, Bool.false_and, Bool.false_eq_true, if_false, hd, if_true, beq_self_eq_true,
    Bool.true_and, decide_eq_true hov]

/-- The fifth digit of the last group, a padding digit. -/
theorem b85_last (t : Nat → Nat) (ig : Option (List Nat)) (k : Bool) (N g l : Nat) (o : List Nat) (len : Int)
    (hlen : len ≤ 0) :
    a2bB85Loop t ig k N (g + 2) [] len ⟨l, 4, o⟩ =
      if l * 85 + 84 ≥ 2 ^ 32 then .error (err s!"Base85 overflow in hunk starting at byte {(((N : Int) - len).toNat) / 5 * 5}")
      else if (3 + len).toNat = 0 then .error (err "Incomplete Base85 group")
      else if k && nonCanon (l * 85 + 84) (3 + len).toNat then .error (err "Non-zero padding bits")
      else .ok { out := o ++ word4 (l * 85 + 84) (3 + len).toNat } := by
  have h0 : (decide (len ≤ 0) && ((4 : Nat) == 0)) = false := by simp
  have hc : len < 1 := by omega
  have hlt : (3 + len).toNat < 4 := by omega
  rw [a2bB85Loop]
  simp only [h0, Bool.false_eq_true, if_false, show (84 : Nat) < 85 by decide, if_true, beq_self_eq_true,
    Bool.true_and, show (4 + 1 != 5) = false by decide, hc, decide_eq_true hlt, Bool.and_true]
  by_cases hov : l * 85 + 84 ≥ 2 ^ 32
  · simp [hov]
  · by_cases hz : (3 + len).toNat = 0
    · simp [hz, hov]
    · by_cases hk : (k && nonCanon (l * 85 + 84) (3 + len).toNat) = true
      · simp [hz, hov, hk]
      · have hk' : (k && nonCanon (l * 85 + 84) (3 + len).toNat) = false := by simpa using hk
        simp only [hov, hz, hk', decide_false, Bool.false_eq_true, if_false]
        rw [b85_stop t ig k N g _ _ (by omega)]

theorem b85_dI (t : Nat → Nat) (ig : Option (List Nat)) (k : Bool) (N f c v l p : Nat) (o r : List Nat) (len : Int)
    (hv : t c = v) (h85 : v < 85) (hlen : 0 < len) (hp : p < 4) :
    a2bB85Loop t ig k N (f + 1) (c :: r) len ⟨l, p, o⟩ = a2bB85Loop t ig k N f r (len - 1) ⟨l * 85 + v, p + 1, o⟩ := by
  have h1 : decide (len ≤ 0) = false := by simp; omega
  have h2 : (p == 4) = false := by simp; omega
  have h3 : (p + 1 != 5) = true := by simp; omega
  simp only [a2bB85Loop, h1, Bool.false_and, Bool.false_eq_true, if_false, hv, h85, if_true, h2, h3]

theorem b85_d5I (t : Nat → Nat) (ig : Option (List Nat)) (k : Bool) (N f c v l : Nat) (o r : List Nat) (len : Int)
    (hv : t c = v) (h85 : v < 85) (hlen : 0 < len) (hov : l * 85 + v < 2 ^ 32) :
    a2bB85Loop t ig k N (f + 1) (c :: r) len ⟨l, 4, o⟩ =
      a2bB85Loop t ig k N f r (len - 1) ⟨0, 0, o ++ word4 (l * 85 + v) 4⟩ := by
  have h1 : decide (len ≤ 0) = false := by simp; omega
  have h2 : decide (l * 85 + v ≥ 2 ^ 32) = false := by simp; omega
  have h3 : ¬ len < 1 := by omega
  simp only [a2bB85Loop, h1, Bool.false_and, Bool.false_eq_true, if_false, hv, h85, if_true, h2, beq_self_eq_true,
    Bool.true_and, h3]
  simp

theorem b85_nI (t : Nat → Nat) (ig : Option (List Nat)) (k : Bool) (N f l p : Nat) (o : List Nat) (len : Int)
    (hp0 : p ≠ 0) (hp : p < 4) :
    a2bB85Loop t ig k N (f + 1) [] len ⟨l, p, o⟩ = a2bB85Loop t ig k N f [] (len - 1) ⟨l * 85 + 84, p + 1, o⟩ := by
  have h1 : (p == 0) = false := by simpa using hp0
  have h2 : (p == 4) = false := by simp; omega
  have h3 : (p + 1 != 5) = true := by simp; omega
  simp only [a2bB85Loop, h1, Bool.and_false, Bool.false_eq_true, if_false, h2, h3]
  simp

/-- What the loop ends with, for the last group. -/
def Tail85 (R : Py St85) (L i0 p : Nat) : Prop :=
  (L ≥ 2 ^ 32 → R = .error (err (ovf85 (5 * i0)))) ∧
  (L < 2 ^ 32 → p = 1 → R = .error (err "Incomplete Base85 group")) ∧
  (L < 2 ^ 32 → p ≠ 1 → (∃ st, R = .ok st) ∨ R = .error (err "Non-zero padding bits"))

theorem tail85_of (k : Bool) (t : Nat → Nat) (ig : Option (List Nat)) (N g l i0 p : Nat) (o : List Nat) (len : Int)
    (hlen : len = (p : Int) - 4) (hp : 1 ≤ p) (hp4 : p ≤ 4) (hN : N = 5 * i0 + p) :
    Tail85 (a2bB85Loop t ig k N (g + 2) [] len ⟨l, 4, o⟩) (l * 85 + 84) i0 p := by
  rw [b85_last t ig k N g l o len (by omega)]
  have hm : (((N : Int) - len).toNat) / 5 * 5 = 5 * i0 := by omega
  have hc : (3 + len).toNat = p - 1 := by omega
  refine ⟨fun h => ?_, fun h h1 => ?_, fun h h1 => ?_⟩
  · rw [if_pos h, hm]; rfl
  · rw [if_neg (by omega), hc, h1]; rfl
  · rw [if_neg (by omega), hc, if_neg (by omega)]
    split
    · right; rfl
    · left; exact ⟨_, rfl⟩

theorem fin85 (R : Py St85) (L i0 p : Nat) (hT : Tail85 R L i0 p) (vs : List Nat) (hg : groups85 vs = [L])
    (hl : vs.length = p) (hp : 1 ≤ p) (hp4 : p ≤ 4) :
    (∀ i, firstOver (groups85 vs) = some i → R = .error (err (ovf85 (5 * (i0 + i))))) ∧
    (firstOver (groups85 vs) = none → vs.length % 5 = 1 → R = .error (err "Incomplete Base85 group")) ∧
    (firstOver (groups85 vs) = none → vs.length % 5 ≠ 1 →
      (∃ st, R = .ok st) ∨ R = .error (err "Non-zero padding bits")) := by
  obtain ⟨t1, t2, t3⟩ := hT
  rw [hg, hl]
  simp only [firstOver, Option.map_none]
  by_cases hL : L ≥ 2 ^ 32
  · simp only [if_pos hL]
    refine ⟨fun i hi => ?_, fun h => ?_, fun h => ?_⟩
    · simp only [Option.some.injEq] at hi
      subst hi
      simpa using t1 hL
    · cases h
    · cases h
  · simp only [if_neg hL]
    refine ⟨fun i hi => ?_, fun _ h => t2 (by omega) (by omega), fun _ h => t3 (by omega) (by omega)⟩
    cases hi

theorem b85_digits (t : Nat → Nat) (ig : Option (List Nat)) (k : Bool) (N : Nat) :
    ∀ (n : Nat) (cs o : List Nat) (f i0 : Nat), cs.length ≤ n → (∀ c ∈ cs, t c < 85) → N = 5 * i0 + cs.length →
      cs.length + 6 ≤ f →
      (∀ i, firstOver (groups85 (cs.map t)) = some i →
        a2bB85Loop t ig k N f cs cs.length ⟨0, 0, o⟩ = .error (err (ovf85 (5 * (i0 + i))))) ∧
      (firstOver (groups85 (cs.map t)) = none → (cs.map t).length % 5 = 1 →
        a2bB85Loop t ig k N f cs cs.length ⟨0, 0, o⟩ = .error (err "Incomplete Base85 group")) ∧
      (firstOver (groups85 (cs.map t)) = none → (cs.map t).length % 5 ≠ 1 →
        (∃ st, a2bB85Loop t ig k N f cs cs.length ⟨0, 0, o⟩ = .ok st) ∨
          a2bB85Loop t ig k N f cs cs.length ⟨0, 0, o⟩ = .error (err "Non-zero padding bits")) := by
  intro n
  induction n with
  | zero =>
    intro cs o f i0 h _ _ hf
    have : cs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp at hf; omega⟩
    refine ⟨fun i hi => (by cases hi), fun _ h => (by simp at h), fun _ _ => Or.inl ⟨_, b85_stop t ig k N g 0 o (by simp)⟩⟩
  | succ n ih =>
    intro cs o f i0 h hd hN hf
    match cs, h, hd, hN, hf with
    | [], _, _, _, hf =>
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp at hf; omega⟩
      refine ⟨fun i hi => (by cases hi), fun _ h => (by simp at h), fun _ _ => Or.inl ⟨_, b85_stop t ig k N g 0 o (by simp)⟩⟩
    | [c0], _, hd, hN, hf =>
      have d0 := hd c0 (by simp)
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 6 := ⟨f - 6, by simp at hf; omega⟩
      have e : a2bB85Loop t ig k N (g + 6) [c0] ([c0].length : Int) ⟨0, 0, o⟩ =
          a2bB85Loop t ig k N (g + 2) [] (1 - 1 - 1 - 1 - 1) ⟨(((0 * 85 + t c0) * 85 + 84) * 85 + 84) * 85 + 84, 4, o⟩ := by
        rw [show g + 6 = (g + 5) + 1 from rfl, show (([c0].length : Nat) : Int) = 1 from rfl,
          b85_dI t ig k N (g + 5) c0 (t c0) 0 0 o [] 1 rfl d0 (by decide) (by decide),
          show g + 5 = (g + 4) + 1 from rfl, b85_nI t ig k N (g + 4) _ 1 o _ (by decide) (by decide),
          show g + 4 = (g + 3) + 1 from rfl, b85_nI t ig k N (g + 3) _ 2 o _ (by decide) (by decide),
          show g + 3 = (g + 2) + 1 from rfl, b85_nI t ig k N (g + 2) _ 3 o _ (by decide) (by decide)]
      rw [e]
      exact fin85 _ _ i0 1 (tail85_of k t ig N g _ i0 1 o _ (by omega) (by decide) (by decide) (by simpa using hN)) _
        (by simp [groups85, val85]) (by simp) (by decide) (by decide)
    | [c0, c1], _, hd, hN, hf =>
      have d0 := hd c0 (by simp)
      have d1 := hd c1 (by simp)
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 6 := ⟨f - 6, by simp at hf; omega⟩
      have e : a2bB85Loop t ig k N (g + 6) [c0, c1] ([c0, c1].length : Int) ⟨0, 0, o⟩ =
          a2bB85Loop t ig k N (g + 2) [] (2 - 1 - 1 - 1 - 1) ⟨(((0 * 85 + t c0) * 85 + t c1) * 85 + 84) * 85 + 84, 4, o⟩ := by
        rw [show g + 6 = (g + 5) + 1 from rfl, show (([c0, c1].length : Nat) : Int) = 2 from rfl,
          b85_dI t ig k N (g + 5) c0 (t c0) 0 0 o [c1] 2 rfl d0 (by decide) (by decide),
          show g + 5 = (g + 4) + 1 from rfl, b85_dI t ig k N (g + 4) c1 (t c1) _ 1 o [] _ rfl d1 (by decide) (by decide),
          show g + 4 = (g + 3) + 1 from rfl, b85_nI t ig k N (g + 3) _ 2 o _ (by decide) (by decide),
          show g + 3 = (g + 2) + 1 from rfl, b85_nI t ig k N (g + 2) _ 3 o _ (by decide) (by decide)]
      rw [e]
      exact fin85 _ _ i0 2 (tail85_of k t ig N g _ i0 2 o _ (by omega) (by decide) (by decide) (by simpa using hN)) _
        (by simp [groups85, val85]) (by simp) (by decide) (by decide)
    | [c0, c1, c2], _, hd, hN, hf =>
      have d0 := hd c0 (by simp)
      have d1 := hd c1 (by simp)
      have d2 := hd c2 (by simp)
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 6 := ⟨f - 6, by simp at hf; omega⟩
      have e : a2bB85Loop t ig k N (g + 6) [c0, c1, c2] ([c0, c1, c2].length : Int) ⟨0, 0, o⟩ =
          a2bB85Loop t ig k N (g + 2) [] (3 - 1 - 1 - 1 - 1) ⟨(((0 * 85 + t c0) * 85 + t c1) * 85 + t c2) * 85 + 84, 4, o⟩ := by
        rw [show g + 6 = (g + 5) + 1 from rfl, show (([c0, c1, c2].length : Nat) : Int) = 3 from rfl,
          b85_dI t ig k N (g + 5) c0 (t c0) 0 0 o [c1, c2] 3 rfl d0 (by decide) (by decide),
          show g + 5 = (g + 4) + 1 from rfl, b85_dI t ig k N (g + 4) c1 (t c1) _ 1 o [c2] _ rfl d1 (by decide) (by decide),
          show g + 4 = (g + 3) + 1 from rfl, b85_dI t ig k N (g + 3) c2 (t c2) _ 2 o [] _ rfl d2 (by decide) (by decide),
          show g + 3 = (g + 2) + 1 from rfl, b85_nI t ig k N (g + 2) _ 3 o _ (by decide) (by decide)]
      rw [e]
      exact fin85 _ _ i0 3 (tail85_of k t ig N g _ i0 3 o _ (by omega) (by decide) (by decide) (by simpa using hN)) _
        (by simp [groups85, val85]) (by simp) (by decide) (by decide)
    | [c0, c1, c2, c3], _, hd, hN, hf =>
      have d0 := hd c0 (by simp)
      have d1 := hd c1 (by simp)
      have d2 := hd c2 (by simp)
      have d3 := hd c3 (by simp)
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 6 := ⟨f - 6, by simp at hf; omega⟩
      have e : a2bB85Loop t ig k N (g + 6) [c0, c1, c2, c3] ([c0, c1, c2, c3].length : Int) ⟨0, 0, o⟩ =
          a2bB85Loop t ig k N (g + 2) [] (4 - 1 - 1 - 1 - 1) ⟨(((0 * 85 + t c0) * 85 + t c1) * 85 + t c2) * 85 + t c3, 4, o⟩ := by
        rw [show g + 6 = (g + 5) + 1 from rfl, show (([c0, c1, c2, c3].length : Nat) : Int) = 4 from rfl,
          b85_dI t ig k N (g + 5) c0 (t c0) 0 0 o [c1, c2, c3] 4 rfl d0 (by decide) (by decide),
          show g + 5 = (g + 4) + 1 from rfl, b85_dI t ig k N (g + 4) c1 (t c1) _ 1 o [c2, c3] _ rfl d1 (by decide) (by decide),
          show g + 4 = (g + 3) + 1 from rfl, b85_dI t ig k N (g + 3) c2 (t c2) _ 2 o [c3] _ rfl d2 (by decide) (by decide),
          show g + 3 = (g + 2) + 1 from rfl, b85_dI t ig k N (g + 2) c3 (t c3) _ 3 o [] _ rfl d3 (by decide) (by decide)]
      rw [e]
      exact fin85 _ _ i0 4 (tail85_of k t ig N g _ i0 4 o _ (by omega) (by decide) (by decide) (by simpa using hN)) _
        (by simp [groups85, val85]) (by simp) (by decide) (by decide)
    | c0 :: c1 :: c2 :: c3 :: c4 :: r, h, hd, hN, hf =>
      have d0 := hd c0 (by simp)
      have d1 := hd c1 (by simp)
      have d2 := hd c2 (by simp)
      have d3 := hd c3 (by simp)
      have d4 := hd c4 (by simp)
      have hr : ∀ c ∈ r, t c < 85 := fun c hc => hd c (by simp [hc])
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 5 := ⟨f - 5, by simp at hf; omega⟩
      have hl : (((c0 :: c1 :: c2 :: c3 :: c4 :: r).length : Nat) : Int) = (r.length : Int) + 5 := by simp; omega
      have e : a2bB85Loop t ig k N (g + 5) (c0 :: c1 :: c2 :: c3 :: c4 :: r) ((c0 :: c1 :: c2 :: c3 :: c4 :: r).length : Int)
            ⟨0, 0, o⟩ =
          a2bB85Loop t ig k N (g + 1) (c4 :: r) ((r.length : Int) + 5 - 1 - 1 - 1 - 1)
            ⟨(((0 * 85 + t c0) * 85 + t c1) * 85 + t c2) * 85 + t c3, 4, o⟩ := by
        rw [hl, show g + 5 = (g + 4) + 1 from rfl,
          b85_dI t ig k N (g + 4) c0 (t c0) 0 0 o _ _ rfl d0 (by omega) (by decide),
          show g + 4 = (g + 3) + 1 from rfl, b85_dI t ig k N (g + 3) c1 (t c1) _ 1 o _ _ rfl d1 (by omega) (by decide),
          show g + 3 = (g + 2) + 1 from rfl, b85_dI t ig k N (g + 2) c2 (t c2) _ 2 o _ _ rfl d2 (by omega) (by decide),
          show g + 2 = (g + 1) + 1 from rfl, b85_dI t ig k N (g + 1) c3 (t c3) _ 3 o _ _ rfl d3 (by omega) (by decide)]
      rw [e]
      generalize hL : (((0 * 85 + t c0) * 85 + t c1) * 85 + t c2) * 85 + t c3 = l4
      have hgr : groups85 ((c0 :: c1 :: c2 :: c3 :: c4 :: r).map t) = (l4 * 85 + t c4) :: groups85 (r.map t) := by
        rw [← hL]; simp [groups85, val85]
      rw [hgr]
      by_cases hov : l4 * 85 + t c4 ≥ 2 ^ 32
      · have hfo : firstOver ((l4 * 85 + t c4) :: groups85 (r.map t)) = some 0 := by simp [firstOver, hov]
        rw [hfo]
        refine ⟨fun i hi => ?_, fun h => ?_, fun h => ?_⟩
        rotate_left
        · cases h
        · cases h
        simp only [Option.some.injEq] at hi
        subst hi
        rw [b85_ov5 t ig k N g c4 l4 o r _ d4 (by omega) hov]
        have hm : (((N : Int) - ((r.length : Int) + 5 - 1 - 1 - 1 - 1)).toNat) / 5 * 5 = 5 * (i0 + 0) := by
          simp at hN; omega
        rw [hm]; rfl
      · have hfo : firstOver ((l4 * 85 + t c4) :: groups85 (r.map t)) = (firstOver (groups85 (r.map t))).map (· + 1) := by
          simp [firstOver, hov]
        rw [hfo, b85_d5I t ig k N g c4 (t c4) l4 o r _ rfl d4 (by omega) (by omega)]
        have e2 : (r.length : Int) + 5 - 1 - 1 - 1 - 1 - 1 = r.length := by omega
        rw [e2]
        obtain ⟨i1, i2, i3⟩ := ih r (o ++ word4 (l4 * 85 + t c4) 4) g (i0 + 1) (by simp at h; omega) hr
          (by simp at hN; omega) (by simp at hf; omega)
        have hlm : ((c0 :: c1 :: c2 :: c3 :: c4 :: r).map t).length % 5 = (r.map t).length % 5 := by simp; omega
        rw [hlm]
        refine ⟨fun i hi => ?_, fun h1 h2 => i2 (by simpa using h1) h2, fun h1 h2 => i3 (by simpa using h1) h2⟩
        cases hf2 : firstOver (groups85 (r.map t)) with
        | none => rw [hf2] at hi; cases hi
        | some i' =>
          rw [hf2] at hi
          simp only [Option.map_some, Option.some.injEq] at hi
          subst hi
          rw [i1 i' hf2]
          congr 3
          omega

/-- The group refusals of `a2b_base85`, exactly, for every input of alphabet characters, every alphabet,
`ignorechars` and `canonical`. Cut the digit values into groups of five, the last padded with the largest
digit (84) as the decoder does. If some group does not fit in 32 bits, the decoder raises "Base85
overflow in hunk starting at byte 5i" for the first such group `i`, and only then; otherwise it raises
"Incomplete Base85 group" exactly when the number of digits is one more than a multiple of five. A
body that drops either check, or wraps the group value mod `2 ** 32`, does not satisfy this. -/
def B85GroupRefusals : Prop :=
  ∀ (s : List Nat) (alpha : AlphaArg) (g : List Nat) (k : Bool),
    (alphaChars85 alpha).length = 85 → (∀ x ∈ s, x ∈ alphaChars85 alpha) →
    (∀ i, firstOver (groups85 (s.map (revT (alphaChars85 alpha) none))) = some i →
      a2bB85 (.bytes s) alpha (.bytes g) k = .error (err (ovf85 (5 * i)))) ∧
    ((∃ j, a2bB85 (.bytes s) alpha (.bytes g) k = .error (err (ovf85 j))) ↔
      firstOver (groups85 (s.map (revT (alphaChars85 alpha) none))) ≠ none) ∧
    (a2bB85 (.bytes s) alpha (.bytes g) k = .error (err "Incomplete Base85 group") ↔
      firstOver (groups85 (s.map (revT (alphaChars85 alpha) none))) = none ∧ s.length % 5 = 1)

theorem b85GroupRefusals_proven : B85GroupRefusals := by
  intro s alpha g k hA hs
  rw [a2bB85_eq alpha hA]
  have hd : ∀ c ∈ s, revT (alphaChars85 alpha) none c < 85 := by
    intro c hc
    have := revT_mem_any _ none c (hs c hc) (by simp)
    omega
  obtain ⟨c1, c2, c3⟩ := b85_digits (revT (alphaChars85 alpha) none) (if g.isEmpty then none else some g) k s.length
    s.length s [] (s.length + 6) 0 (Nat.le_refl _) hd (by simp) (Nat.le_refl _)
  have e0 : ({} : St85) = ⟨0, 0, []⟩ := rfl
  rw [e0]
  generalize hR : a2bB85Loop (revT (alphaChars85 alpha) none) (if g.isEmpty then none else some g) k s.length
    (s.length + 6) s s.length ⟨0, 0, []⟩ = R at c1 c2 c3
  generalize hF : firstOver (groups85 (s.map (revT (alphaChars85 alpha) none))) = F at c1 c2 c3
  simp only [List.length_map] at c2 c3
  have hne1 : ∀ j, ovf85 j ≠ "Incomplete Base85 group" := fun j => ovf85_ne j _ (by decide)
  have hne2 : ∀ j, ovf85 j ≠ "Non-zero padding bits" := fun j => ovf85_ne j _ (by decide)
  have einj : ∀ a b : String, (Except.error (err a) : Py (List Nat)) = .error (err b) → a = b := by
    intro a b h
    simp only [err, Except.error.injEq, PyExc.named.injEq, true_and] at h
    exact h
  refine ⟨fun i hi => ?_, ⟨fun ⟨j, hj⟩ => ?_, fun hn => ?_⟩, ⟨fun h => ?_, fun ⟨h1, h2⟩ => ?_⟩⟩
  · rw [c1 i hi, Nat.zero_add]; rfl
  · intro hFn
    by_cases h5 : s.length % 5 = 1
    · rw [c2 hFn h5] at hj
      exact hne1 j (einj _ _ hj).symm
    · rcases c3 hFn h5 with ⟨st, hst⟩ | hst
      · rw [hst] at hj; cases hj
      · rw [hst] at hj; exact hne2 j (einj _ _ hj).symm
  · obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hn
    exact ⟨5 * i, by rw [c1 i hi, Nat.zero_add]; rfl⟩
  · cases hF2 : F with
    | some i =>
      rw [c1 i hF2] at h
      exact absurd (einj _ _ h) (hne1 _)
    | none =>
      refine ⟨rfl, ?_⟩
      by_cases h5 : s.length % 5 = 1
      · exact h5
      · rcases c3 hF2 h5 with ⟨st, hst⟩ | hst
        · rw [hst] at h; cases h
        · rw [hst] at h; exact absurd (einj _ _ h) (by decide)
  · rw [c2 h1 h2]; rfl

end PyLean.TextLibs.Binascii
