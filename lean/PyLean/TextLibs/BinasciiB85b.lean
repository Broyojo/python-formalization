import PyLean.TextLibs.BinasciiB85

/-!
The base85 decoder on what the encoder writes, for `canonical` either way and `pad` either way, and the
statements about `a2b_base85` and `b2a_base85` over every option.
-/

namespace PyLean.TextLibs.Binascii

open PyLean

set_option linter.unusedSimpArgs false

theorem b85_dG (t : Nat → Nat) (k : Bool) (N f c v l p : Nat) (o r : List Nat) (len : Int) (hv : t c = v) (h85 : v < 85)
    (hlen : 0 < len) (hp : p < 4) :
    a2bB85Loop t none k N (f + 1) (c :: r) len ⟨l, p, o⟩ =
      a2bB85Loop t none k N f r (len - 1) ⟨l * 85 + v, p + 1, o⟩ := by
  have h1 : decide (len ≤ 0) = false := by simp; omega
  have h2 : (p == 4) = false := by simp; omega
  have h3 : (p + 1 != 5) = true := by simp; omega
  simp only [a2bB85Loop, h1, Bool.false_and, Bool.false_eq_true, if_false, hv, h85, if_true, h2, h3]

theorem b85_d5G (t : Nat → Nat) (k : Bool) (N f c v l : Nat) (o r : List Nat) (len : Int) (hv : t c = v) (h85 : v < 85)
    (hlen : 0 < len) (hov : l * 85 + v < 2 ^ 32) :
    a2bB85Loop t none k N (f + 1) (c :: r) len ⟨l, 4, o⟩ =
      a2bB85Loop t none k N f r (len - 1) ⟨0, 0, o ++ word4 (l * 85 + v) 4⟩ := by
  have h1 : decide (len ≤ 0) = false := by simp; omega
  have h2 : decide (l * 85 + v ≥ 2 ^ 32) = false := by simp; omega
  have h3 : ¬ len < 1 := by omega
  simp only [a2bB85Loop, h1, Bool.false_and, Bool.false_eq_true, if_false, hv, h85, if_true, h2, beq_self_eq_true,
    Bool.true_and, h3]
  simp

theorem b85_nG (t : Nat → Nat) (k : Bool) (N f l p : Nat) (o : List Nat) (len : Int) (hp0 : p ≠ 0) (hp : p < 4) :
    a2bB85Loop t none k N (f + 1) [] len ⟨l, p, o⟩ =
      a2bB85Loop t none k N f [] (len - 1) ⟨l * 85 + 84, p + 1, o⟩ := by
  have h1 : (p == 0) = false := by simpa using hp0
  have h2 : (p == 4) = false := by simp; omega
  have h3 : (p + 1 != 5) = true := by simp; omega
  simp only [a2bB85Loop, h1, Bool.and_false, Bool.false_eq_true, if_false, h2, h3]
  simp

theorem b85_n5G (t : Nat → Nat) (k : Bool) (N f l kk : Nat) (o : List Nat) (len : Int) (hlen : len = (kk : Int) - 3)
    (hk0 : kk ≠ 0) (hk : kk < 4) (hov : l * 85 + 84 < 2 ^ 32) (hc : nonCanon (l * 85 + 84) kk = false) :
    a2bB85Loop t none k N (f + 1) [] len ⟨l, 4, o⟩ =
      a2bB85Loop t none k N f [] (len - 1) ⟨0, 0, o ++ word4 (l * 85 + 84) kk⟩ := by
  have h2 : decide (l * 85 + 84 ≥ 2 ^ 32) = false := by simp; omega
  have h3 : len < 1 := by omega
  have h4 : (3 + len).toNat = kk := by omega
  have h5 : ¬ kk = 0 := hk0
  have h6 : ¬ 4294967212 ≤ l * 85 := by omega
  simp only [a2bB85Loop, Bool.and_false, Bool.false_eq_true, if_false, beq_self_eq_true, Bool.true_and, h3, if_true, h4,
    h5, hc]
  simp [h6]

theorem b85_groupG (a : List Nat) (t : Nat → Nat) (ht : ∀ v, v < 85 → t (a.getD v 0) = v) (k : Bool) (N f w : Nat)
    (o r : List Nat) (len : Int) (hw : w < 2 ^ 32) (hlen : len = (r.length : Int) + 5) :
    a2bB85Loop t none k N (f + 5) (digits85 a w ++ r) len ⟨0, 0, o⟩ =
      a2bB85Loop t none k N f r r.length ⟨0, 0, o ++ word4 w 4⟩ := by
  rw [digits85_eq]
  simp only [List.cons_append, List.nil_append]
  rw [b85_dG t k N (f + 4) _ _ 0 0 o _ len (ht _ (Nat.mod_lt _ (by decide))) (Nat.mod_lt _ (by decide)) (by omega) (by omega),
    b85_dG t k N (f + 3) _ _ _ _ o _ _ (ht _ (Nat.mod_lt _ (by decide))) (Nat.mod_lt _ (by decide)) (by omega) (by omega),
    b85_dG t k N (f + 2) _ _ _ _ o _ _ (ht _ (Nat.mod_lt _ (by decide))) (Nat.mod_lt _ (by decide)) (by omega) (by omega),
    b85_dG t k N (f + 1) _ _ _ _ o _ _ (ht _ (Nat.mod_lt _ (by decide))) (Nat.mod_lt _ (by decide)) (by omega) (by omega)]
  have hw2 : (((0 * 85 + w / 52200625 % 85) * 85 + w / 614125 % 85) * 85 + w / 7225 % 85) * 85 + w / 85 % 85 = w / 85 := by
    omega
  have e : 0 + 1 + 1 + 1 + 1 = 4 := rfl
  rw [hw2, e, b85_d5G t k N f _ _ _ o _ _ (ht _ (Nat.mod_lt _ (by decide))) (Nat.mod_lt _ (by decide)) (by omega) (by omega)]
  have hw3 : w / 85 * 85 + w / 1 % 85 = w := by omega
  have e2 : len - 1 - 1 - 1 - 1 - 1 = (r.length : Int) := by omega
  rw [hw3, e2]

/-- What `binascii_b2a_base85_impl` writes before wrapping, with `fe` as the fuel of its loop. -/
def enc85P (a : List Nat) (fe : Nat) (d : List Nat) (pad : Bool) : List Nat :=
  (fullB85 a fe d).1 ++
    (if (fullB85 a fe d).2.isEmpty then [] else
      (digits85 a (wordOf (fullB85 a fe d).2)).take (if pad then 5 else (fullB85 a fe d).2.length + 1))

/-- The zero bytes `pad=True` adds. -/
def zeros85 (d : List Nat) (pad : Bool) : List Nat := if pad then List.replicate ((4 - d.length % 4) % 4) 0 else []

theorem enc85P_nil (a : List Nat) (fe : Nat) (pad : Bool) : enc85P a fe [] pad = [] := by
  unfold enc85P
  rw [full85_short a [] fe (by simp)]
  rfl

theorem enc85P_short (a d : List Nat) (fe : Nat) (pad : Bool) (h : d.length < 4) (hd : d ≠ []) :
    enc85P a fe d pad = (digits85 a (wordOf d)).take (if pad then 5 else d.length + 1) := by
  unfold enc85P
  rw [full85_short a d fe h]
  cases d with
  | nil => exact absurd rfl hd
  | cons x r => rfl

theorem enc85P_4 (a : List Nat) (fe x y z e : Nat) (r : List Nat) (pad : Bool) :
    enc85P a (fe + 1) (x :: y :: z :: e :: r) pad = digits85 a (wordOf [x, y, z, e]) ++ enc85P a fe r pad := by
  have ht : (x :: y :: z :: e :: r).take 4 = [x, y, z, e] := rfl
  have hd : (x :: y :: z :: e :: r).drop 4 = r := rfl
  have hc : fullB85 a (fe + 1) (x :: y :: z :: e :: r) =
      (digits85 a (wordOf [x, y, z, e]) ++ (fullB85 a fe r).1, (fullB85 a fe r).2) := by
    rw [fullB85, if_pos (by simp only [List.length_cons]; omega)]
    simp only [ht, hd]
  unfold enc85P
  rw [hc]
  simp only [List.append_assoc]

theorem nc1 (w : Nat) (hw : w % 16777216 = 0) : nonCanon (w + (614124 - w % 614125)) 1 = false := by
  have h1 : (w + (614124 - w % 614125)) / 16777216 * 16777216 = w := by omega
  have h3 : (w + (614124 - w % 614125)) / 614125 = w / 614125 := by omega
  have e : nonCanon (w + (614124 - w % 614125)) 1 =
      ((w + (614124 - w % 614125)) / 16777216 * 16777216 / 614125 != (w + (614124 - w % 614125)) / 614125) := rfl
  rw [e, h1, h3]
  simp

theorem nc2 (w : Nat) (hw : w % 65536 = 0) : nonCanon (w + (7224 - w % 7225)) 2 = false := by
  have h1 : (w + (7224 - w % 7225)) / 65536 * 65536 = w := by omega
  have h3 : (w + (7224 - w % 7225)) / 7225 = w / 7225 := by omega
  have e : nonCanon (w + (7224 - w % 7225)) 2 =
      ((w + (7224 - w % 7225)) / 65536 * 65536 / 7225 != (w + (7224 - w % 7225)) / 7225) := rfl
  rw [e, h1, h3]
  simp

theorem nc3 (w : Nat) (hw : w % 256 = 0) : nonCanon (w + (84 - w % 85)) 3 = false := by
  have h1 : (w + (84 - w % 85)) / 256 * 256 = w := by omega
  have h3 : (w + (84 - w % 85)) / 85 = w / 85 := by omega
  have e : nonCanon (w + (84 - w % 85)) 3 = ((w + (84 - w % 85)) / 256 * 256 / 85 != (w + (84 - w % 85)) / 85) := rfl
  rw [e, h1, h3]
  simp

theorem dec85G_main (a : List Nat) (t : Nat → Nat) (ht : ∀ v, v < 85 → t (a.getD v 0) = v) (k : Bool) (N : Nat) (pad : Bool) :
    ∀ (n : Nat) (d : List Nat), d.length ≤ n → (∀ x ∈ d, x < 256) → ∀ (fe f : Nat) (o : List Nat),
      d.length ≤ fe → (enc85P a fe d pad).length + 6 ≤ f →
      a2bB85Loop t none k N f (enc85P a fe d pad) (enc85P a fe d pad).length ⟨0, 0, o⟩ =
        .ok ⟨0, 0, o ++ d ++ zeros85 d pad⟩ := by
  intro n
  induction n with
  | zero =>
    intro d h _ fe f o _ hf
    have : d = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [enc85P_nil] at hf ⊢
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simpa [zeros85] using b85_stop t none k N g 0 o (by omega)
  | succ n ih =>
    intro d h hb fe f o hfe hf
    match d, h, hb, hfe, hf with
    | [], _, _, _, hf =>
      rw [enc85P_nil] at hf ⊢
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      simpa [zeros85] using b85_stop t none k N g 0 o (by omega)
    | [x], _, hb, _, hf =>
      have hx := hb x (by simp)
      rw [enc85P_short a [x] fe pad (by simp) (by simp), wordOf_1] at hf ⊢
      cases pad with
      | true =>
        simp only [if_true, List.take_of_length_le (show (digits85 a (x * 16777216)).length ≤ 5 from by simp [digits85])]
          at hf ⊢
        have hl : (digits85 a (x * 16777216)).length = 5 := by simp [digits85]
        rw [hl] at hf
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 6 := ⟨f - 6, by omega⟩
        have := b85_groupG a t ht k N (g + 1) (x * 16777216) o [] 5 (by omega) (by simp)
        rw [show g + 6 = g + 1 + 5 by omega, show ((digits85 a (x * 16777216)).length : Int) = 5 by rw [hl]; rfl]
        rw [← List.append_nil (digits85 a (x * 16777216)), this]
        rw [show (([] : List Nat).length : Int) = 0 from rfl, b85_stop t none k N g 0 _ (by omega)]
        have hb4 : word4 (x * 16777216) 4 = [x, 0, 0, 0] := by
          rw [word4_4]; simp only [List.cons.injEq, and_true]; refine ⟨by omega, by omega, by omega, by omega⟩
        rw [hb4]
        simp [zeros85]
      | false =>
        simp only [Bool.false_eq_true, if_false, digits85_eq] at hf ⊢
        simp only [List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero, Nat.zero_add] at hf ⊢
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 6 := ⟨f - 6, by omega⟩
        generalize hw : x * 16777216 = w at *
        have hb1 : w ≤ 4278190080 := by omega
        have c0 := Nat.mod_lt (w / 52200625) (show 85 > 0 by decide)
        have c1 := Nat.mod_lt (w / 614125) (show 85 > 0 by decide)
        have e1 := d2 w (by omega)
        have e2 : 0 + 1 + 1 + 1 + 1 = 4 := rfl
        rw [b85_dG t k N (g + 5) _ _ 0 0 o _ _ (ht _ c0) c0 (by omega) (by omega),
          b85_dG t k N (g + 4) _ _ _ _ o _ _ (ht _ c1) c1 (by omega) (by omega), e1,
          b85_nG t k N (g + 3) _ _ o _ (by omega) (by omega), b85_nG t k N (g + 2) _ _ o _ (by omega) (by omega), e2,
          b85_n5G t k N (g + 1) _ 1 o _ (by omega) (by decide) (by decide) (by rw [pad3]; omega)
            (by rw [pad3]; exact nc1 w (by omega)),
          b85_stop t none k N g _ _ (by omega), pad3, ← hw, cut1 x _ hx (by omega)]
        simp [zeros85]
    | [x, y], _, hb, _, hf =>
      have hx := hb x (by simp)
      have hy := hb y (by simp)
      rw [enc85P_short a [x, y] fe pad (by simp) (by simp), wordOf_2] at hf ⊢
      cases pad with
      | true =>
        simp only [if_true, List.take_of_length_le (show (digits85 a (x * 16777216 + y * 65536)).length ≤ 5 from by
          simp [digits85])] at hf ⊢
        have hl : (digits85 a (x * 16777216 + y * 65536)).length = 5 := by simp [digits85]
        rw [hl] at hf
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 6 := ⟨f - 6, by omega⟩
        have := b85_groupG a t ht k N (g + 1) (x * 16777216 + y * 65536) o [] 5 (by omega) (by simp)
        rw [show g + 6 = g + 1 + 5 by omega, show ((digits85 a (x * 16777216 + y * 65536)).length : Int) = 5 by rw [hl]; rfl]
        rw [← List.append_nil (digits85 a (x * 16777216 + y * 65536)), this]
        rw [show (([] : List Nat).length : Int) = 0 from rfl, b85_stop t none k N g 0 _ (by omega)]
        have hb4 : word4 (x * 16777216 + y * 65536) 4 = [x, y, 0, 0] := by
          rw [word4_4]; simp only [List.cons.injEq, and_true]; refine ⟨by omega, by omega, by omega, by omega⟩
        rw [hb4]
        simp [zeros85]
      | false =>
        simp only [Bool.false_eq_true, if_false, digits85_eq] at hf ⊢
        simp only [List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero, Nat.zero_add] at hf ⊢
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 6 := ⟨f - 6, by omega⟩
        generalize hw : x * 16777216 + y * 65536 = w at *
        have hb1 : w ≤ 4294901760 := by omega
        have c0 := Nat.mod_lt (w / 52200625) (show 85 > 0 by decide)
        have c1 := Nat.mod_lt (w / 614125) (show 85 > 0 by decide)
        have c2 := Nat.mod_lt (w / 7225) (show 85 > 0 by decide)
        have e1 := d3 w (by omega)
        have e2 : 0 + 1 + 1 + 1 + 1 = 4 := rfl
        rw [b85_dG t k N (g + 5) _ _ 0 0 o _ _ (ht _ c0) c0 (by omega) (by omega),
          b85_dG t k N (g + 4) _ _ _ _ o _ _ (ht _ c1) c1 (by omega) (by omega),
          b85_dG t k N (g + 3) _ _ _ _ o _ _ (ht _ c2) c2 (by omega) (by omega), e1,
          b85_nG t k N (g + 2) _ _ o _ (by omega) (by omega), e2,
          b85_n5G t k N (g + 1) _ 2 o _ (by omega) (by decide) (by decide) (by rw [pad2]; omega)
            (by rw [pad2]; exact nc2 w (by omega)),
          b85_stop t none k N g _ _ (by omega), pad2, ← hw, cut2 x y _ hx hy (by omega)]
        simp [zeros85]
    | [x, y, z], _, hb, _, hf =>
      have hx := hb x (by simp)
      have hy := hb y (by simp)
      have hz := hb z (by simp)
      rw [enc85P_short a [x, y, z] fe pad (by simp) (by simp), wordOf_3] at hf ⊢
      cases pad with
      | true =>
        simp only [if_true, List.take_of_length_le (show (digits85 a (x * 16777216 + y * 65536 + z * 256)).length ≤ 5 from
          by simp [digits85])] at hf ⊢
        have hl : (digits85 a (x * 16777216 + y * 65536 + z * 256)).length = 5 := by simp [digits85]
        rw [hl] at hf
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 6 := ⟨f - 6, by omega⟩
        have := b85_groupG a t ht k N (g + 1) (x * 16777216 + y * 65536 + z * 256) o [] 5 (by omega) (by simp)
        rw [show g + 6 = g + 1 + 5 by omega,
          show ((digits85 a (x * 16777216 + y * 65536 + z * 256)).length : Int) = 5 by rw [hl]; rfl]
        rw [← List.append_nil (digits85 a (x * 16777216 + y * 65536 + z * 256)), this]
        rw [show (([] : List Nat).length : Int) = 0 from rfl, b85_stop t none k N g 0 _ (by omega)]
        have hb4 : word4 (x * 16777216 + y * 65536 + z * 256) 4 = [x, y, z, 0] := by
          rw [word4_4]; simp only [List.cons.injEq, and_true]; refine ⟨by omega, by omega, by omega, by omega⟩
        rw [hb4]
        simp [zeros85]
      | false =>
        simp only [Bool.false_eq_true, if_false, digits85_eq] at hf ⊢
        simp only [List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero, Nat.zero_add] at hf ⊢
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 6 := ⟨f - 6, by omega⟩
        generalize hw : x * 16777216 + y * 65536 + z * 256 = w at *
        have hb1 : w ≤ 4294967040 := by omega
        have c0 := Nat.mod_lt (w / 52200625) (show 85 > 0 by decide)
        have c1 := Nat.mod_lt (w / 614125) (show 85 > 0 by decide)
        have c2 := Nat.mod_lt (w / 7225) (show 85 > 0 by decide)
        have c3 := Nat.mod_lt (w / 85) (show 85 > 0 by decide)
        have e1 := d4 w (by omega)
        have e2 : 0 + 1 + 1 + 1 + 1 = 4 := rfl
        rw [b85_dG t k N (g + 5) _ _ 0 0 o _ _ (ht _ c0) c0 (by omega) (by omega),
          b85_dG t k N (g + 4) _ _ _ _ o _ _ (ht _ c1) c1 (by omega) (by omega),
          b85_dG t k N (g + 3) _ _ _ _ o _ _ (ht _ c2) c2 (by omega) (by omega),
          b85_dG t k N (g + 2) _ _ _ _ o _ _ (ht _ c3) c3 (by omega) (by omega), e1, e2,
          b85_n5G t k N (g + 1) _ 3 o _ (by omega) (by decide) (by decide) (by rw [pad1]; omega)
            (by rw [pad1]; exact nc3 w (by omega)),
          b85_stop t none k N g _ _ (by omega), pad1, ← hw, cut3 x y z _ hx hy hz (by omega)]
        simp [zeros85]
    | x :: y :: z :: e :: r, h, hb, hfe, hf =>
      have hx := hb x (by simp)
      have hy := hb y (by simp)
      have hz := hb z (by simp)
      have he := hb e (by simp)
      obtain ⟨fe, rfl⟩ : ∃ k, fe = k + 1 := ⟨fe - 1, by simp only [List.length_cons] at hfe; omega⟩
      rw [enc85P_4] at hf ⊢
      have hlenD : (digits85 a (wordOf [x, y, z, e])).length = 5 := rfl
      rw [List.length_append, hlenD] at hf ⊢
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 5 := ⟨f - 5, by omega⟩
      rw [b85_groupG a t ht k N g _ o _ _ (by rw [wordOf_4]; omega) (by push_cast; omega)]
      have hr := ih r (by simp only [List.length_cons] at h; omega) (fun y hy => hb y (by simp [hy])) fe g
        (o ++ word4 (wordOf [x, y, z, e]) 4) (by simp only [List.length_cons] at hfe; omega) (by omega)
      have hbytes : word4 (wordOf [x, y, z, e]) 4 = [x, y, z, e] := by
        rw [word4_4, wordOf_4]
        simp only [List.cons.injEq, and_true]
        refine ⟨by omega, by omega, by omega, by omega⟩
      rw [hbytes] at hr ⊢
      rw [hr]
      have hz : zeros85 (x :: y :: z :: e :: r) pad = zeros85 r pad := by
        simp only [zeros85, List.length_cons]
        have : (r.length + 1 + 1 + 1 + 1) % 4 = r.length % 4 := by omega
        rw [this]
      rw [hz]
      simp [List.append_assoc]

end PyLean.TextLibs.Binascii
