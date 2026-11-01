import PyLean.TextLibs.BinasciiProps4

/-!
Ascii85. On top of the base85 digit arithmetic, `z` and `y` fold whole words, and the decoder pads with
`u` rather than padding the data it is given: its loop runs over `b + b'uuuu'`, so the group it was in
the middle of completes and what remains of the `u`s tells how many bytes to cut.
-/

namespace PyLean.TextLibs.Binascii

open PyLean

set_option linter.unusedSimpArgs false

/-- The encoding as a recursion. A cut last word is never folded, whatever it holds. -/
def a85R (fs : Bool) : List Nat → List Nat
  | a :: b :: c :: e :: r => fn85 a85char true fs (w4 a b c e) ++ a85R fs r
  | [] => []
  | [a] => (word5 a85char (w4 a 0 0 0)).take 2
  | [a, b] => (word5 a85char (w4 a b 0 0)).take 3
  | [a, b, c] => (word5 a85char (w4 a b c 0)).take 4

theorem word5_a85_zero : word5 a85char 0 = List.replicate 5 (a85char 0) := rfl

/-- The tail of `_85encode` for a word with a zero low byte: the fold undone, then the cut. -/
theorem tail_chunk (w k : Nat) (fs : Bool) (hw : w % 256 = 0) :
    (let last := fn85 a85char true fs w
     let last := if last == [122] then List.replicate 5 (a85char 0) else last
     last.take (last.length - k)) = (word5 a85char w).take (5 - k) := by
  by_cases h0 : w = 0
  · subst h0
    simp [fn85, word5_a85_zero]
  · have hs : ¬(w = 0x20202020) := by
      intro h
      rw [h] at hw
      omega
    have h1 : (w == 0) = false := beq_false_of_ne h0
    have h2 : (w == 0x20202020) = false := beq_false_of_ne hs
    have hl : (word5 a85char w).length = 5 := rfl
    have hn : (word5 a85char w == [122]) = false := by
      simp [word5]
    simp [fn85, h1, h2, hn, hl]

/-- One chunk through the end of `_85encode`. `x` stays opaque here: unfolding `fn85` in a kernel
term makes it compare a symbolic word with `0x20202020` in unary. -/
theorem finish_one (p : Nat) (hp : p ≠ 0) (x : List Nat) :
    finishChunks p false a85char [x] =
      (if x == [122] then List.replicate 5 (a85char 0) else x).take
        ((if x == [122] then List.replicate 5 (a85char 0) else x).length - p) := by
  simp [finishChunks, hp]

theorem enc85_a85 (fs : Bool) : ∀ (n : Nat) (d : List Nat), d.length ≤ n →
    enc85 d a85char false true fs = a85R fs d := by
  intro n
  induction n with
  | zero =>
    intro d h
    have : d = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rfl
  | succ n ih =>
    intro d h
    match d, h with
    | [], _ => rfl
    | [a], _ =>
      have e := tail_chunk (w4 a 0 0 0) 3 fs (by simp only [w4]; omega)
      have hw : words4 ([a] ++ List.replicate 3 0).length ([a] ++ List.replicate 3 0) = [w4 a 0 0 0] := by
        have : a * 256 * 256 * 256 = w4 a 0 0 0 := by simp [w4]; omega
        simp [words4, this]
      rw [enc85_eq, show (4 - [a].length % 4) % 4 = 3 from rfl, hw, List.map_cons, List.map_nil,
        finish_one 3 (by omega)]
      exact e
    | [a, b], _ =>
      have e := tail_chunk (w4 a b 0 0) 2 fs (by simp only [w4]; omega)
      have hw : words4 ([a, b] ++ List.replicate 2 0).length ([a, b] ++ List.replicate 2 0) = [w4 a b 0 0] := by
        have : (a * 256 + b) * 256 * 256 = w4 a b 0 0 := by simp [w4]; omega
        simp [words4, this]
      rw [enc85_eq, show (4 - [a, b].length % 4) % 4 = 2 from rfl, hw, List.map_cons, List.map_nil,
        finish_one 2 (by omega)]
      exact e
    | [a, b, c], _ =>
      have e := tail_chunk (w4 a b c 0) 1 fs (by simp only [w4]; omega)
      have hw : words4 ([a, b, c] ++ List.replicate 1 0).length ([a, b, c] ++ List.replicate 1 0) =
          [w4 a b c 0] := by
        have : ((a * 256 + b) * 256 + c) * 256 = w4 a b c 0 := by simp [w4]; omega
        simp [words4, this]
      rw [enc85_eq, show (4 - [a, b, c].length % 4) % 4 = 1 from rfl, hw, List.map_cons, List.map_nil,
        finish_one 1 (by omega)]
      exact e
    | a :: b :: c :: e :: r, h =>
      rw [enc85_cons, ih r (by simp at h; omega)]
      simp only [a85R]

/-- A digit of the decoder's alphabet. -/
theorem a85_digit (i : Nat) (h : i < 85) : 33 ≤ a85char i ∧ a85char i ≤ 117 ∧ a85char i - 33 = i := by
  simp only [a85char]
  omega

/-- Digits into `curr`, short of a group. -/
theorem a85Loop_digit (fs : Bool) (ig : List Nat) (i : Nat) (h : i < 85) (rest curr dec : List Nat)
    (hl : curr.length ≠ 4) :
    a85Loop fs ig (a85char i :: rest) curr dec = a85Loop fs ig rest (curr ++ [a85char i]) dec := by
  obtain ⟨h1, h2, _⟩ := a85_digit i h
  simp only [a85Loop]
  rw [if_pos ⟨h1, h2⟩, if_neg (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)]

/-- The fifth digit completes the group. -/
theorem a85Loop_fifth (fs : Bool) (ig : List Nat) (d1 d2 d3 d4 d5 : Nat) (h1 : d1 < 85) (h2 : d2 < 85)
    (h3 : d3 < 85) (h4 : d4 < 85) (h5 : d5 < 85) (rest dec : List Nat)
    (hv : d1 * 52200625 + d2 * 614125 + d3 * 7225 + d4 * 85 + d5 < 2 ^ 32) :
    a85Loop fs ig (a85char d1 :: a85char d2 :: a85char d3 :: a85char d4 :: a85char d5 :: rest) [] dec =
      a85Loop fs ig rest []
        ((packI (d1 * 52200625 + d2 * 614125 + d3 * 7225 + d4 * 85 + d5)).reverse ++ dec) := by
  rw [a85Loop_digit fs ig d1 h1 _ _ _ (by simp), a85Loop_digit fs ig d2 h2 _ _ _ (by simp),
    a85Loop_digit fs ig d3 h3 _ _ _ (by simp), a85Loop_digit fs ig d4 h4 _ _ _ (by simp)]
  obtain ⟨g1, g2, g3⟩ := a85_digit d1 h1
  obtain ⟨k1, k2, k3⟩ := a85_digit d2 h2
  obtain ⟨l1, l2, l3⟩ := a85_digit d3 h3
  obtain ⟨m1, m2, m3⟩ := a85_digit d4 h4
  obtain ⟨n1, n2, n3⟩ := a85_digit d5 h5
  have hacc : ([] ++ [a85char d1] ++ [a85char d2] ++ [a85char d3] ++ [a85char d4] ++ [a85char d5]).foldl
      (fun a c => 85 * a + (c - 33)) 0 = d1 * 52200625 + d2 * 614125 + d3 * 7225 + d4 * 85 + d5 := by
    simp only [List.nil_append, List.cons_append, List.foldl_cons, List.foldl_nil, g3, k3, l3, m3, n3]
    omega
  conv => lhs; unfold a85Loop
  rw [if_pos ⟨n1, n2⟩]
  simp only [List.length_append, List.length_cons, List.length_nil, hacc]
  simp only [show (0 + 1 + 1 + 1 + 1 + 1 = 5) from rfl, if_true]
  rw [if_neg (Nat.not_le.2 hv)]

/-- `u` is the top digit. -/
theorem a85_u : a85char 84 = 117 := rfl

/-- The decoder's loop on an encoding followed by the four `u`s: the bytes, some more that the cut
removes, and as many `u`s left over as say how many. -/
theorem a85_go (fs : Bool) (ig : List Nat) : ∀ (n : Nat) (d : List Nat), d.length ≤ n →
    (∀ x ∈ d, x < 256) → ∀ dec : List Nat,
    ∃ curr z : List Nat, a85Loop fs ig (a85R fs d ++ [117, 117, 117, 117]) [] dec =
        .ok (curr, z.reverse ++ d.reverse ++ dec) ∧
      z.length = padOf d ∧ curr.length = 4 - padOf d := by
  intro n
  induction n with
  | zero =>
    intro d h _ dec
    have : d = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact ⟨[117, 117, 117, 117], [], by simp [a85R, a85Loop], rfl, rfl⟩
  | succ n ih =>
    intro d h hb dec
    match d, h, hb with
    | [], _, _ => exact ⟨[117, 117, 117, 117], [], by simp [a85R, a85Loop], rfl, rfl⟩
    | [a], _, hb =>
      have ha : a < 256 := hb a (by simp)
      have hw : w4 a 0 0 0 < 2 ^ 32 := by simp only [w4]; omega
      obtain ⟨h1, h2, _, _, _⟩ := word5_digits _ hw
      obtain ⟨t1, t2⟩ := tail2 (w4 a 0 0 0) _ rfl
      have hw' : w4 a 0 0 0 = a * 16777216 := by simp only [w4]; omega
      have hv : (w4 a 0 0 0 / 614125 / 85) * 52200625 + (w4 a 0 0 0 / 614125 % 85) * 614125 +
          84 * 7225 + 84 * 85 + 84 < 2 ^ 32 := by omega
      have ht : a85R fs [a] ++ [117, 117, 117, 117] =
          [a85char (w4 a 0 0 0 / 614125 / 85), a85char (w4 a 0 0 0 / 614125 % 85),
           a85char 84, a85char 84, a85char 84, 117] := by
        simp [a85R, word5, a85_u]
      rw [ht, a85Loop_fifth fs ig _ _ _ _ _ h1 h2 (by omega) (by omega) (by omega) _ _ hv]
      generalize hx : (w4 a 0 0 0 / 614125 / 85) * 52200625 + (w4 a 0 0 0 / 614125 % 85) * 614125 +
        84 * 7225 + 84 * 85 + 84 = x
      rw [hx, hw'] at t1 t2
      have e := top1 x a ha t1 t2
      have hu : a85Loop fs ig [117] [] ((packI x).reverse ++ dec) = .ok ([117], (packI x).reverse ++ dec) := by
        simp [a85Loop]
      refine ⟨[117], [x / 2 ^ 16 % 256, x / 2 ^ 8 % 256, x % 256], ?_, rfl, rfl⟩
      rw [hu]
      simp [packI, e]
    | [a, b], _, hb =>
      have ha : a < 256 := hb a (by simp)
      have hb' : b < 256 := hb b (by simp)
      have hw : w4 a b 0 0 < 2 ^ 32 := by simp only [w4]; omega
      obtain ⟨h1, h2, h3, _, _⟩ := word5_digits _ hw
      obtain ⟨t1, t2⟩ := tail3 (w4 a b 0 0) _ rfl
      have hw' : w4 a b 0 0 = a * 16777216 + b * 65536 := by simp only [w4]; omega
      have hv : (w4 a b 0 0 / 614125 / 85) * 52200625 + (w4 a b 0 0 / 614125 % 85) * 614125 +
          ((w4 a b 0 0 / 85 % 7225) / 85) * 7225 + 84 * 85 + 84 < 2 ^ 32 := by omega
      have ht : a85R fs [a, b] ++ [117, 117, 117, 117] =
          [a85char (w4 a b 0 0 / 614125 / 85), a85char (w4 a b 0 0 / 614125 % 85),
           a85char ((w4 a b 0 0 / 85 % 7225) / 85), a85char 84, a85char 84, 117, 117] := by
        simp [a85R, word5, a85_u]
      rw [ht, a85Loop_fifth fs ig _ _ _ _ _ h1 h2 h3 (by omega) (by omega) _ _ hv]
      generalize hx : (w4 a b 0 0 / 614125 / 85) * 52200625 + (w4 a b 0 0 / 614125 % 85) * 614125 +
        ((w4 a b 0 0 / 85 % 7225) / 85) * 7225 + 84 * 85 + 84 = x
      rw [hx, hw'] at t1 t2
      obtain ⟨e1, e2⟩ := top2 x a b ha hb' t1 t2
      have hu : a85Loop fs ig [117, 117] [] ((packI x).reverse ++ dec) =
          .ok ([117, 117], (packI x).reverse ++ dec) := by
        simp [a85Loop]
      refine ⟨[117, 117], [x / 2 ^ 8 % 256, x % 256], ?_, rfl, rfl⟩
      rw [hu]
      simp [packI, e1, e2]
    | [a, b, c], _, hb =>
      have ha : a < 256 := hb a (by simp)
      have hb' : b < 256 := hb b (by simp)
      have hc : c < 256 := hb c (by simp)
      have hw : w4 a b c 0 < 2 ^ 32 := by simp only [w4]; omega
      obtain ⟨h1, h2, h3, h4, _⟩ := word5_digits _ hw
      obtain ⟨t1, t2⟩ := tail4 (w4 a b c 0) _ rfl
      have hw' : w4 a b c 0 = a * 16777216 + b * 65536 + c * 256 := by simp only [w4]; omega
      have hv : (w4 a b c 0 / 614125 / 85) * 52200625 + (w4 a b c 0 / 614125 % 85) * 614125 +
          ((w4 a b c 0 / 85 % 7225) / 85) * 7225 + ((w4 a b c 0 / 85 % 7225) % 85) * 85 + 84 < 2 ^ 32 := by
        omega
      have ht : a85R fs [a, b, c] ++ [117, 117, 117, 117] =
          [a85char (w4 a b c 0 / 614125 / 85), a85char (w4 a b c 0 / 614125 % 85),
           a85char ((w4 a b c 0 / 85 % 7225) / 85), a85char ((w4 a b c 0 / 85 % 7225) % 85), a85char 84,
           117, 117, 117] := by
        simp [a85R, word5, a85_u]
      rw [ht, a85Loop_fifth fs ig _ _ _ _ _ h1 h2 h3 h4 (by omega) _ _ hv]
      generalize hx : (w4 a b c 0 / 614125 / 85) * 52200625 + (w4 a b c 0 / 614125 % 85) * 614125 +
        ((w4 a b c 0 / 85 % 7225) / 85) * 7225 + ((w4 a b c 0 / 85 % 7225) % 85) * 85 + 84 = x
      rw [hx, hw'] at t1 t2
      obtain ⟨e1, e2, e3⟩ := top3 x a b c ha hb' hc t1 t2
      have hu : a85Loop fs ig [117, 117, 117] [] ((packI x).reverse ++ dec) =
          .ok ([117, 117, 117], (packI x).reverse ++ dec) := by
        simp [a85Loop]
      refine ⟨[117, 117, 117], [x % 256], ?_, rfl, rfl⟩
      rw [hu]
      simp [packI, e1, e2, e3]
    | a :: b :: c :: e :: r, h, hb =>
      have ha : a < 256 := hb a (by simp)
      have hb' : b < 256 := hb b (by simp)
      have hc : c < 256 := hb c (by simp)
      have he : e < 256 := hb e (by simp)
      have hwl : w4 a b c e < 2 ^ 32 := by simp only [w4]; omega
      have hpad : padOf (a :: b :: c :: e :: r) = padOf r := by
        simp only [padOf, List.length_cons]
        omega
      have hrev : (a :: b :: c :: e :: r).reverse = r.reverse ++ [e, c, b, a] := by simp
      have hr : ∀ x ∈ r, x < 256 := fun x hx => hb x (by simp [hx])
      simp only [a85R, hpad, hrev]
      have hgroup : ∀ (t : List Nat) (D : List Nat), ∃ D',
          a85Loop fs ig (fn85 a85char true fs (w4 a b c e) ++ t) [] D = a85Loop fs ig t [] D' ∧
            D' = [e, c, b, a] ++ D := by
        intro t D
        by_cases h0 : w4 a b c e = 0
        · have e0 : a = 0 ∧ b = 0 ∧ c = 0 ∧ e = 0 := by
            simp only [w4] at h0
            omega
          obtain ⟨rfl, rfl, rfl, rfl⟩ := e0
          refine ⟨_, ?_, rfl⟩
          simp [fn85, w4, a85Loop]
        · by_cases h1 : fs = true ∧ w4 a b c e = 0x20202020
          · obtain ⟨hf, h2⟩ := h1
            have e0 : a = 32 ∧ b = 32 ∧ c = 32 ∧ e = 32 := by
              simp only [w4] at h2
              omega
            obtain ⟨rfl, rfl, rfl, rfl⟩ := e0
            refine ⟨_, ?_, rfl⟩
            simp [fn85, w4, a85Loop, hf]
          · have hq : fn85 a85char true fs (w4 a b c e) = word5 a85char (w4 a b c e) := by
              have g0 : (w4 a b c e == 0) = false := beq_false_of_ne h0
              have g1 : (fs && w4 a b c e == 0x20202020) = false := by
                cases hf : fs with
                | false => rfl
                | true =>
                  have : w4 a b c e ≠ 0x20202020 := fun hh => h1 ⟨hf, hh⟩
                  simpa using this
              simp [fn85, g0, g1]
            rw [hq]
            obtain ⟨d1, d2, d3, d4, d5⟩ := word5_digits _ hwl
            have hval := word5_value _ hwl
            have hs : word5 a85char (w4 a b c e) ++ t =
                a85char (w4 a b c e / 614125 / 85) :: a85char (w4 a b c e / 614125 % 85) ::
                  a85char ((w4 a b c e / 85 % 7225) / 85) :: a85char ((w4 a b c e / 85 % 7225) % 85) ::
                  a85char (w4 a b c e % 85) :: t := rfl
            rw [hs, a85Loop_fifth fs ig _ _ _ _ _ d1 d2 d3 d4 d5 _ _ (by rw [hval]; exact hwl), hval]
            have hp : packI (w4 a b c e) = [a, b, c, e] := by
              simp only [packI, w4, List.cons.injEq, and_true]
              omega
            exact ⟨_, rfl, by rw [hp]; rfl⟩
      obtain ⟨D', h1, h2⟩ := hgroup (a85R fs r ++ [117, 117, 117, 117]) dec
      obtain ⟨curr, z, r1, r2, r3⟩ := ih r (by simp at h; omega) hr D'
      refine ⟨curr, z, ?_, r2, r3⟩
      rw [List.append_assoc, h1, r1, h2]
      simp [List.append_assoc]

/-- `a85decode(a85encode(d, foldspaces=f), foldspaces=f) == d`, through the `z` and `y` folds and a cut
last group. Wrapping and the Adobe framing are `A85WrapRoundTrip`. -/
def A85RoundTrip : Prop :=
  ∀ (d : List Nat) (fs : Bool), (∀ x ∈ d, x < 256) →
    a85decode (.bytes (a85encode d fs 0 false false)) fs false defaultIgnore = .ok d

theorem a85RoundTrip_proven : A85RoundTrip := by
  intro d fs hd
  have he : enc85 d a85char false true fs = a85R fs d := enc85_a85 fs d.length d (Nat.le_refl _)
  obtain ⟨curr, z, h1, h2, h3⟩ := a85_go fs defaultIgnore d.length d (Nat.le_refl _) hd []
  have hl : padOf d < 4 := by unfold padOf; omega
  have hA : a85encode d fs 0 false false = a85R fs d := by
    simp [a85encode, he]
  rw [hA]
  simp only [a85decode, bytesFromDecodeData, bind, Except.bind, Bool.false_eq_true, if_false, pure,
    Except.pure]
  rw [h1]
  have hp : 4 - curr.length = padOf d := by omega
  simp only [hp, List.append_nil, List.reverse_append, List.reverse_reverse]
  by_cases h0 : padOf d = 0
  · have : z = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [h0]
  · rw [if_pos h0]
    have hlen : (d ++ z).length - padOf d = d.length := by
      simp only [List.length_append]
      omega
    rw [hlen, List.take_left']
    rfl

/-- The same with `wrapcol` and `adobe`, for which the statement is the one the docs give: decoding
with `adobe` and the default `ignorechars`, which include the newline `wrapcol` inserts. Held on
CPython in the difftest's sweep. A proof needs `a85Loop` shown to skip the newlines and the framing
shown to survive `chunksOf`, whose first chunk holds `<~` because the width is at least 2. -/
def A85WrapRoundTrip : Prop :=
  ∀ (d : List Nat) (fs adobe : Bool) (wrapcol : Int), (∀ x ∈ d, x < 256) →
    a85decode (.bytes (a85encode d fs wrapcol false adobe)) fs adobe defaultIgnore = .ok d

end PyLean.TextLibs.Binascii
