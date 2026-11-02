import PyLean.TextLibs.BinasciiProps3

/-!
The 85-based codecs. `enc85` is a pipeline of `struct.unpack`, `map` and a cut of the last group; the
first part of this file shows it is a recursion on four bytes at a time. The rest is digit arithmetic:
the decoder pads a cut group with the top digit, and the top bytes survive because
`85 ^ p - 1 < 256 ^ p`.
-/

namespace PyLean.TextLibs.Binascii

open PyLean

set_option linter.unusedSimpArgs false

/-! ### `enc85` as a recursion -/

theorem words4_fuel : ∀ (f g : Nat) (l : List Nat), l.length ≤ f → l.length ≤ g →
    words4 f l = words4 g l := by
  intro f
  induction f with
  | zero =>
    intro g l h _
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    cases g <;> rfl
  | succ f ih =>
    intro g l h1 h2
    cases g with
    | zero =>
      have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      rfl
    | succ g =>
      cases l with
      | nil => rfl
      | cons x r =>
        simp only [words4]
        rw [ih g _ (by simp at h1 ⊢; omega) (by simp at h2 ⊢; omega)]

/-- The end of `_85encode` (a specification; `BinasciiC.lean` has the function of 3.15.2). -/
def finishChunks (padding : Nat) (pad : Bool) (chars : Nat → Nat) (chunks : List (List Nat)) : List Nat :=
  (if padding ≠ 0 ∧ (!pad) = true then
    let last := chunks.getLast?.getD []
    let last := if last == [122] then List.replicate 5 (chars 0) else last
    chunks.dropLast ++ [last.take (last.length - padding)]
  else chunks).flatten

theorem finish_cons (p : Nat) (pad : Bool) (chars : Nat → Nat) (x : List Nat) (l : List (List Nat))
    (h : l ≠ []) : finishChunks p pad chars (x :: l) = x ++ finishChunks p pad chars l := by
  by_cases hc : p ≠ 0 ∧ (!pad) = true
  · have h1 : (x :: l).getLast? = l.getLast? := by
      cases l with
      | nil => exact absurd rfl h
      | cons y t => rfl
    have h2 : (x :: l).dropLast = x :: l.dropLast := by
      cases l with
      | nil => exact absurd rfl h
      | cons y t => rfl
    simp only [finishChunks, if_pos hc, h1, h2, List.cons_append, List.flatten_cons]
  · simp only [finishChunks, if_neg hc, List.flatten_cons]

/-- The chunk of one word. -/
def fn85 (chars : Nat → Nat) (fnuls fspaces : Bool) (w : Nat) : List Nat :=
  if fnuls && w == 0 then [122]
  else if fspaces && w == 0x20202020 then [121]
  else word5 chars w

theorem enc85_eq (b : List Nat) (chars : Nat → Nat) (pad fnuls fspaces : Bool) :
    enc85 b chars pad fnuls fspaces =
      finishChunks ((4 - b.length % 4) % 4) pad chars
        ((words4 (b ++ List.replicate ((4 - b.length % 4) % 4) 0).length
          (b ++ List.replicate ((4 - b.length % 4) % 4) 0)).map (fn85 chars fnuls fspaces)) := rfl

/-- A big-endian word. -/
def w4 (a b c e : Nat) : Nat := a * 16777216 + b * 65536 + c * 256 + e

theorem words4_step (f a b c e : Nat) (r : List Nat) :
    words4 (f + 1) (a :: b :: c :: e :: r) = w4 a b c e :: words4 f r := by
  have : ((([a, b, c, e] : List Nat).foldl (fun x b => x * 256 + b) 0)) = w4 a b c e := by
    simp [w4]
    omega
  simp only [words4, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, this]

theorem words4_ne (f : Nat) (l : List Nat) (hf : 0 < f) (h : l ≠ []) : words4 f l ≠ [] := by
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  cases l with
  | nil => exact absurd rfl h
  | cons x r => simp [words4]

/-- Four bytes at the front are one chunk, and then the rest of the encoding. -/
theorem enc85_cons (a b c e : Nat) (r : List Nat) (chars : Nat → Nat) (pad fnuls fspaces : Bool) :
    enc85 (a :: b :: c :: e :: r) chars pad fnuls fspaces =
      fn85 chars fnuls fspaces (w4 a b c e) ++ enc85 r chars pad fnuls fspaces := by
  have hp : (4 - (a :: b :: c :: e :: r).length % 4) % 4 = (4 - r.length % 4) % 4 := by
    simp only [List.length_cons]
    omega
  rw [enc85_eq, enc85_eq, hp]
  generalize hq : (4 - r.length % 4) % 4 = p
  have happ : (a :: b :: c :: e :: r) ++ List.replicate p 0 =
      a :: b :: c :: e :: (r ++ List.replicate p 0) := rfl
  rw [happ]
  simp only [List.length_cons]
  rw [words4_step]
  rw [words4_fuel _ (r ++ List.replicate p 0).length (r ++ List.replicate p 0) (by omega) (by omega)]
  simp only [List.map_cons]
  by_cases hnil : r ++ List.replicate p 0 = []
  · have hr : r = [] := (List.append_eq_nil_iff.1 hnil).1
    subst hr
    have hp0 : p = 0 := by simpa using hq.symm
    subst hp0
    simp [finishChunks]
  · have hne : (words4 (r ++ List.replicate p 0).length (r ++ List.replicate p 0)).map
        (fn85 chars fnuls fspaces) ≠ [] := by
      intro h0
      have := List.map_eq_nil_iff.1 h0
      exact words4_ne _ _ (List.length_pos_iff.2 hnil) hnil this
    exact finish_cons _ _ _ _ _ hne

/-! ### Base85 digits -/

theorem b85dec_char : ∀ i, i < 85 → b85dec (b85char i) = some i := by decide +kernel

theorem b85char_84 : b85char 84 = 126 := by decide +kernel

theorem word5_digits (w : Nat) (h : w < 2 ^ 32) :
    (w / 614125 / 85 < 85) ∧ (w / 614125 % 85 < 85) ∧ ((w / 85 % 7225) / 85 < 85) ∧
    ((w / 85 % 7225) % 85 < 85) ∧ (w % 85 < 85) := by
  omega

/-- Five digits, read back. -/
theorem b85_chunk (d1 d2 d3 d4 d5 : Nat) (h1 : d1 < 85) (h2 : d2 < 85) (h3 : d3 < 85) (h4 : d4 < 85)
    (h5 : d5 < 85) :
    b85Chunk [b85char d1, b85char d2, b85char d3, b85char d4, b85char d5] 0 0 =
      .inr (d1 * 52200625 + d2 * 614125 + d3 * 7225 + d4 * 85 + d5) := by
  simp only [b85Chunk, b85dec_char _ h1, b85dec_char _ h2, b85dec_char _ h3, b85dec_char _ h4,
    b85dec_char _ h5]
  congr 1
  omega

theorem b85Loop_step (f : Nat) (d1 d2 d3 d4 d5 : Nat) (rest : List Nat) (i : Nat)
    (h1 : d1 < 85) (h2 : d2 < 85) (h3 : d3 < 85) (h4 : d4 < 85) (h5 : d5 < 85)
    (hv : d1 * 52200625 + d2 * 614125 + d3 * 7225 + d4 * 85 + d5 < 2 ^ 32) :
    b85Loop (f + 1) (b85char d1 :: b85char d2 :: b85char d3 :: b85char d4 :: b85char d5 :: rest) i =
      (do return packI (d1 * 52200625 + d2 * 614125 + d3 * 7225 + d4 * 85 + d5) ++
        (← b85Loop f rest (i + 5))) := by
  simp only [b85Loop, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero]
  rw [b85_chunk d1 d2 d3 d4 d5 h1 h2 h3 h4 h5]
  simp only [if_neg (Nat.not_le.2 hv)]

theorem word5_value (w : Nat) (h : w < 2 ^ 32) :
    (w / 614125 / 85) * 52200625 + (w / 614125 % 85) * 614125 + ((w / 85 % 7225) / 85) * 7225 +
      ((w / 85 % 7225) % 85) * 85 + w % 85 = w := by
  omega

/-- The digits of a word, one division by 85 at a time. -/
theorem word5_parts (w : Nat) : ∃ q r0 r1 r2,
    w = q * 614125 + r2 * 7225 + r1 * 85 + r0 ∧ r0 < 85 ∧ r1 < 85 ∧ r2 < 85 ∧
    w / 614125 = q ∧ (w / 85 % 7225) / 85 = r2 ∧ (w / 85 % 7225) % 85 = r1 ∧ w % 85 = r0 := by
  have e1 : w / 7225 = w / 85 / 85 := by rw [Nat.div_div_eq_div_mul]
  have e2 : w / 614125 = w / 85 / 85 / 85 := by rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  refine ⟨w / 85 / 85 / 85, w % 85, w / 85 % 85, w / 85 / 85 % 85, ?_, by omega, by omega, by omega,
    e2, ?_, ?_, rfl⟩
  · generalize w / 85 / 85 / 85 = q at *
    omega
  · omega
  · omega

/-- Cut to two digits and padded with `~`: the value rises by less than `85 ^ 3`. -/
theorem tail2 (w x : Nat) (h : x = (w / 614125 / 85) * 52200625 + (w / 614125 % 85) * 614125 +
    84 * 7225 + 84 * 85 + 84) : w ≤ x ∧ x ≤ w + 614124 := by
  obtain ⟨q, r0, r1, r2, e, h0, h1, h2, e1, _, _, _⟩ := word5_parts w
  rw [e1] at h
  have : (q / 85) * 52200625 + (q % 85) * 614125 = q * 614125 := by omega
  omega

/-- Cut to three digits: less than `85 ^ 2`. -/
theorem tail3 (w x : Nat) (h : x = (w / 614125 / 85) * 52200625 + (w / 614125 % 85) * 614125 +
    ((w / 85 % 7225) / 85) * 7225 + 84 * 85 + 84) : w ≤ x ∧ x ≤ w + 7224 := by
  obtain ⟨q, r0, r1, r2, e, h0, h1, h2, e1, e2, _, _⟩ := word5_parts w
  rw [e1, e2] at h
  have : (q / 85) * 52200625 + (q % 85) * 614125 = q * 614125 := by omega
  omega

/-- Cut to four digits: less than `85`. -/
theorem tail4 (w x : Nat) (h : x = (w / 614125 / 85) * 52200625 + (w / 614125 % 85) * 614125 +
    ((w / 85 % 7225) / 85) * 7225 + ((w / 85 % 7225) % 85) * 85 + 84) : w ≤ x ∧ x ≤ w + 84 := by
  obtain ⟨q, r0, r1, r2, e, h0, h1, h2, e1, e2, e3, _⟩ := word5_parts w
  rw [e1, e2, e3] at h
  have : (q / 85) * 52200625 + (q % 85) * 614125 = q * 614125 := by omega
  omega

theorem top1 (x a : Nat) (ha : a < 256) (h1 : a * 16777216 ≤ x) (h2 : x ≤ a * 16777216 + 614124) :
    x / 2 ^ 24 % 256 = a := by
  omega

theorem top2 (x a b : Nat) (ha : a < 256) (hb : b < 256) (h1 : a * 16777216 + b * 65536 ≤ x)
    (h2 : x ≤ a * 16777216 + b * 65536 + 7224) :
    x / 2 ^ 24 % 256 = a ∧ x / 2 ^ 16 % 256 = b := by
  omega

theorem top3 (x a b c : Nat) (ha : a < 256) (hb : b < 256) (hc : c < 256)
    (h1 : a * 16777216 + b * 65536 + c * 256 ≤ x) (h2 : x ≤ a * 16777216 + b * 65536 + c * 256 + 84) :
    x / 2 ^ 24 % 256 = a ∧ x / 2 ^ 16 % 256 = b ∧ x / 2 ^ 8 % 256 = c := by
  omega

/-- The encoding as a recursion: whole words, then a cut last word. -/
def enc85R (chars : Nat → Nat) : List Nat → List Nat
  | a :: b :: c :: e :: r => word5 chars (w4 a b c e) ++ enc85R chars r
  | [] => []
  | [a] => (word5 chars (w4 a 0 0 0)).take 2
  | [a, b] => (word5 chars (w4 a b 0 0)).take 3
  | [a, b, c] => (word5 chars (w4 a b c 0)).take 4

theorem enc85_rec (chars : Nat → Nat) : ∀ (n : Nat) (d : List Nat), d.length ≤ n →
    enc85 d chars false false false = enc85R chars d := by
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
      show _ = (word5 chars (w4 a 0 0 0)).take 2
      have : a * 256 * 256 * 256 = w4 a 0 0 0 := by simp [w4]; omega
      simp [enc85, words4, this, fn85, word5]
    | [a, b], _ =>
      show _ = (word5 chars (w4 a b 0 0)).take 3
      have : (a * 256 + b) * 256 * 256 = w4 a b 0 0 := by simp [w4]; omega
      simp [enc85, words4, this, fn85, word5]
    | [a, b, c], _ =>
      show _ = (word5 chars (w4 a b c 0)).take 4
      have : ((a * 256 + b) * 256 + c) * 256 = w4 a b c 0 := by simp [w4]; omega
      simp [enc85, words4, this, fn85, word5]
    | a :: b :: c :: e :: r, h =>
      rw [enc85_cons]
      have := ih r (by simp at h; omega)
      simp only [fn85, Bool.false_and, Bool.false_eq_true, if_false, this, enc85R]

/-- The padding the decoder adds. -/
def padOf (d : List Nat) : Nat := (4 - d.length % 4) % 4

theorem b85_go : ∀ (n : Nat) (d : List Nat), d.length ≤ n → (∀ x ∈ d, x < 256) →
    ∀ (f i : Nat), (enc85R b85char d ++ List.replicate (padOf d) 126).length ≤ f →
    ∃ z, b85Loop f (enc85R b85char d ++ List.replicate (padOf d) 126) i = .ok (d ++ z) ∧
      z.length = padOf d := by
  intro n
  induction n with
  | zero =>
    intro d h _ f i _
    have : d = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    refine ⟨[], ?_, rfl⟩
    cases f <;> rfl
  | succ n ih =>
    intro d h hb f i hf
    match d, h, hb, hf with
    | [], _, _, _ =>
      refine ⟨[], ?_, rfl⟩
      cases f <;> rfl
    | [a], _, hb, hf =>
      have ha : a < 256 := hb a (by simp)
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [enc85R, word5, padOf] at hf; omega⟩
      have hw : w4 a 0 0 0 < 2 ^ 32 := by simp only [w4]; omega
      obtain ⟨h1, h2, _, _, _⟩ := word5_digits _ hw
      obtain ⟨t1, t2⟩ := tail2 (w4 a 0 0 0) _ rfl
      have hw' : w4 a 0 0 0 = a * 16777216 := by simp only [w4]; omega
      have hv : (w4 a 0 0 0 / 614125 / 85) * 52200625 + (w4 a 0 0 0 / 614125 % 85) * 614125 +
          84 * 7225 + 84 * 85 + 84 < 2 ^ 32 := by omega
      have ht : enc85R b85char [a] ++ List.replicate (padOf [a]) 126 =
          [b85char (w4 a 0 0 0 / 614125 / 85), b85char (w4 a 0 0 0 / 614125 % 85),
           b85char 84, b85char 84, b85char 84] := by
        simp [enc85R, word5, padOf, b85char_84]
      rw [ht, b85Loop_step g _ _ _ _ _ [] i h1 h2 (by omega) (by omega) (by omega) hv]
      have hl : b85Loop g [] (i + 5) = .ok [] := by cases g <;> rfl
      simp only [hl, bind, Except.bind, pure, Except.pure]
      generalize hx : (w4 a 0 0 0 / 614125 / 85) * 52200625 + (w4 a 0 0 0 / 614125 % 85) * 614125 +
        84 * 7225 + 84 * 85 + 84 = x
      rw [hx, hw'] at t1 t2
      have e := top1 x a ha t1 t2
      refine ⟨[x / 2 ^ 16 % 256, x / 2 ^ 8 % 256, x % 256], ?_, rfl⟩
      simp [packI, e]
    | [a, b], _, hb, hf =>
      have ha : a < 256 := hb a (by simp)
      have hb' : b < 256 := hb b (by simp)
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [enc85R, word5, padOf] at hf; omega⟩
      have hw : w4 a b 0 0 < 2 ^ 32 := by simp only [w4]; omega
      obtain ⟨h1, h2, h3, _, _⟩ := word5_digits _ hw
      obtain ⟨t1, t2⟩ := tail3 (w4 a b 0 0) _ rfl
      have hw' : w4 a b 0 0 = a * 16777216 + b * 65536 := by simp only [w4]; omega
      have hv : (w4 a b 0 0 / 614125 / 85) * 52200625 + (w4 a b 0 0 / 614125 % 85) * 614125 +
          ((w4 a b 0 0 / 85 % 7225) / 85) * 7225 + 84 * 85 + 84 < 2 ^ 32 := by omega
      have ht : enc85R b85char [a, b] ++ List.replicate (padOf [a, b]) 126 =
          [b85char (w4 a b 0 0 / 614125 / 85), b85char (w4 a b 0 0 / 614125 % 85),
           b85char ((w4 a b 0 0 / 85 % 7225) / 85), b85char 84, b85char 84] := by
        simp [enc85R, word5, padOf, b85char_84]
      rw [ht, b85Loop_step g _ _ _ _ _ [] i h1 h2 h3 (by omega) (by omega) hv]
      have hl : b85Loop g [] (i + 5) = .ok [] := by cases g <;> rfl
      simp only [hl, bind, Except.bind, pure, Except.pure]
      generalize hx : (w4 a b 0 0 / 614125 / 85) * 52200625 + (w4 a b 0 0 / 614125 % 85) * 614125 +
        ((w4 a b 0 0 / 85 % 7225) / 85) * 7225 + 84 * 85 + 84 = x
      rw [hx, hw'] at t1 t2
      obtain ⟨e1, e2⟩ := top2 x a b ha hb' t1 t2
      refine ⟨[x / 2 ^ 8 % 256, x % 256], ?_, rfl⟩
      simp [packI, e1, e2]
    | [a, b, c], _, hb, hf =>
      have ha : a < 256 := hb a (by simp)
      have hb' : b < 256 := hb b (by simp)
      have hc : c < 256 := hb c (by simp)
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [enc85R, word5, padOf] at hf; omega⟩
      have hw : w4 a b c 0 < 2 ^ 32 := by simp only [w4]; omega
      obtain ⟨h1, h2, h3, h4, _⟩ := word5_digits _ hw
      obtain ⟨t1, t2⟩ := tail4 (w4 a b c 0) _ rfl
      have hw' : w4 a b c 0 = a * 16777216 + b * 65536 + c * 256 := by simp only [w4]; omega
      have hv : (w4 a b c 0 / 614125 / 85) * 52200625 + (w4 a b c 0 / 614125 % 85) * 614125 +
          ((w4 a b c 0 / 85 % 7225) / 85) * 7225 + ((w4 a b c 0 / 85 % 7225) % 85) * 85 + 84 < 2 ^ 32 := by
        omega
      have ht : enc85R b85char [a, b, c] ++ List.replicate (padOf [a, b, c]) 126 =
          [b85char (w4 a b c 0 / 614125 / 85), b85char (w4 a b c 0 / 614125 % 85),
           b85char ((w4 a b c 0 / 85 % 7225) / 85), b85char ((w4 a b c 0 / 85 % 7225) % 85),
           b85char 84] := by
        simp [enc85R, word5, padOf, b85char_84]
      rw [ht, b85Loop_step g _ _ _ _ _ [] i h1 h2 h3 h4 (by omega) hv]
      have hl : b85Loop g [] (i + 5) = .ok [] := by cases g <;> rfl
      simp only [hl, bind, Except.bind, pure, Except.pure]
      generalize hx : (w4 a b c 0 / 614125 / 85) * 52200625 + (w4 a b c 0 / 614125 % 85) * 614125 +
        ((w4 a b c 0 / 85 % 7225) / 85) * 7225 + ((w4 a b c 0 / 85 % 7225) % 85) * 85 + 84 = x
      rw [hx, hw'] at t1 t2
      obtain ⟨e1, e2, e3⟩ := top3 x a b c ha hb' hc t1 t2
      refine ⟨[x % 256], ?_, rfl⟩
      simp [packI, e1, e2, e3]
    | a :: b :: c :: e :: r, h, hb, hf =>
      have ha : a < 256 := hb a (by simp)
      have hb' : b < 256 := hb b (by simp)
      have hc : c < 256 := hb c (by simp)
      have he : e < 256 := hb e (by simp)
      have hw : w4 a b c e < 2 ^ 32 := by simp only [w4]; omega
      have hpad : padOf (a :: b :: c :: e :: r) = padOf r := by
        simp only [padOf, List.length_cons]
        omega
      obtain ⟨h1, h2, h3, h4, h5⟩ := word5_digits _ hw
      have hval := word5_value _ hw
      simp only [enc85R, hpad] at hf ⊢
      have hlen : (word5 b85char (w4 a b c e)).length = 5 := rfl
      simp only [List.length_append, hlen] at hf
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      obtain ⟨z, r1, r2⟩ := ih r (by simp at h; omega) (fun x hx => hb x (by simp [hx])) g (i + 5)
        (by simp only [List.length_append]; omega)
      refine ⟨z, ?_, r2⟩
      have hs : word5 b85char (w4 a b c e) ++ (enc85R b85char r ++ List.replicate (padOf r) 126) =
          b85char (w4 a b c e / 614125 / 85) :: b85char (w4 a b c e / 614125 % 85) ::
            b85char ((w4 a b c e / 85 % 7225) / 85) :: b85char ((w4 a b c e / 85 % 7225) % 85) ::
            b85char (w4 a b c e % 85) :: (enc85R b85char r ++ List.replicate (padOf r) 126) := rfl
      rw [List.append_assoc, hs, b85Loop_step g _ _ _ _ _ _ _ h1 h2 h3 h4 h5 (by rw [hval]; exact hw),
        hval, r1]
      have hp : packI (w4 a b c e) = [a, b, c, e] := by
        simp only [packI, w4, List.cons.injEq, and_true]
        omega
      simp [bind, Except.bind, pure, Except.pure, hp]

theorem enc85R_length : ∀ (n : Nat) (d : List Nat), d.length ≤ n →
    ((enc85R b85char d).length + padOf d) % 5 = 0 := by
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
    | [a], _ => simp [enc85R, word5, padOf]
    | [a, b], _ => simp [enc85R, word5, padOf]
    | [a, b, c], _ => simp [enc85R, word5, padOf]
    | a :: b :: c :: e :: r, h =>
      have := ih r (by simp at h; omega)
      have hpad : padOf (a :: b :: c :: e :: r) = padOf r := by
        simp only [padOf, List.length_cons]
        omega
      have hlen : (word5 b85char (w4 a b c e)).length = 5 := rfl
      simp only [enc85R, hpad, List.length_append, hlen]
      omega

/-- `b85decode(b85encode(d)) == d`, including a cut last group. The hypothesis is that `d` holds
bytes. -/
def B85RoundTrip : Prop :=
  ∀ d : List Nat, (∀ x ∈ d, x < 256) → b85decode (.bytes (b85encode d false)) = .ok d

theorem b85RoundTrip_proven : B85RoundTrip := by
  intro d hd
  have he : b85encode d false = enc85R b85char d := enc85_rec b85char d.length d (Nat.le_refl _)
  rw [he]
  have hl := enc85R_length d.length d (Nat.le_refl _)
  have hp : (5 - (enc85R b85char d).length % 5) % 5 = padOf d := by
    have : padOf d < 4 := by unfold padOf; omega
    omega
  simp only [b85decode, bytesFromDecodeData, bind, Except.bind, b85decodeBytes]
  rw [hp]
  obtain ⟨z, h1, h2⟩ := b85_go d.length d (Nat.le_refl _) hd _ 0 (Nat.le_refl _)
  rw [h1]
  simp only [pure, Except.pure]
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

/-! ### z85 -/

/-- The `tr` of `z85encode` and of the decoder's table. -/
theorem z85_back : ∀ i, i < 85 →
    tr (z85alphabet ++ ";_`|~".toList.map Char.toNat) (b85alphabet ++ [0, 0, 0, 0, 0])
      (tr b85alphabet z85alphabet (b85char i)) = b85char i := by
  decide +kernel

theorem word5_mem (w : Nat) (h : w < 2 ^ 32) : ∀ c ∈ word5 b85char w, ∃ i, i < 85 ∧ c = b85char i := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := word5_digits w h
  intro c hc
  simp only [word5, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with hc | hc | hc | hc | hc
  · exact ⟨_, h1, hc⟩
  · exact ⟨_, h2, hc⟩
  · exact ⟨_, h3, hc⟩
  · exact ⟨_, h4, hc⟩
  · exact ⟨_, h5, hc⟩

theorem enc85R_mem : ∀ (n : Nat) (d : List Nat), d.length ≤ n → (∀ x ∈ d, x < 256) →
    ∀ c ∈ enc85R b85char d, ∃ i, i < 85 ∧ c = b85char i := by
  intro n
  induction n with
  | zero =>
    intro d h _ c hc
    have : d = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [enc85R] at hc
  | succ n ih =>
    intro d h hb c hc
    have hw : ∀ a b x e, a < 256 → b < 256 → x < 256 → e < 256 → w4 a b x e < 2 ^ 32 := by
      intro a b x e h1 h2 h3 h4
      simp only [w4]
      omega
    match d, h, hb, hc with
    | [], _, _, hc => simp [enc85R] at hc
    | [a], _, hb, hc =>
      exact word5_mem _ (hw a 0 0 0 (hb a (by simp)) (by omega) (by omega) (by omega)) c
        (List.mem_of_mem_take hc)
    | [a, b], _, hb, hc =>
      exact word5_mem _ (hw a b 0 0 (hb a (by simp)) (hb b (by simp)) (by omega) (by omega)) c
        (List.mem_of_mem_take hc)
    | [a, b, x], _, hb, hc =>
      exact word5_mem _ (hw a b x 0 (hb a (by simp)) (hb b (by simp)) (hb x (by simp)) (by omega)) c
        (List.mem_of_mem_take hc)
    | a :: b :: x :: e :: r, h, hb, hc =>
      simp only [enc85R, List.mem_append] at hc
      rcases hc with hc | hc
      · exact word5_mem _ (hw a b x e (hb a (by simp)) (hb b (by simp)) (hb x (by simp)) (hb e (by simp))) c hc
      · exact ih r (by simp at h; omega) (fun y hy => hb y (by simp [hy])) c hc

/-- `z85decode(z85encode(d)) == d`. -/
def Z85RoundTrip : Prop :=
  ∀ d : List Nat, (∀ x ∈ d, x < 256) → z85decode (.bytes (z85encode d)) = .ok d

theorem z85RoundTrip_proven : Z85RoundTrip := by
  intro d hd
  have he : b85encode d false = enc85R b85char d := enc85_rec b85char d.length d (Nat.le_refl _)
  have hm := enc85R_mem d.length d (Nat.le_refl _) hd
  have hback : ∀ s : List Nat, (∀ c ∈ s, ∃ i, i < 85 ∧ c = b85char i) →
      z85DecodeMap (translate b85alphabet z85alphabet s) = s := by
    intro s
    induction s with
    | nil => intro _; rfl
    | cons c r ih =>
      intro h
      obtain ⟨i, hi, rfl⟩ := h c (by simp)
      have hr := ih (fun x hx => h x (by simp [hx]))
      have e : z85DecodeMap (translate b85alphabet z85alphabet (b85char i :: r)) =
          tr (z85alphabet ++ ";_`|~".toList.map Char.toNat) (b85alphabet ++ [0, 0, 0, 0, 0])
            (tr b85alphabet z85alphabet (b85char i)) ::
            z85DecodeMap (translate b85alphabet z85alphabet r) := rfl
      rw [e, z85_back i hi, hr]
  have hb := b85RoundTrip_proven d hd
  rw [he] at hb
  simp only [z85decode, z85encode, bytesFromDecodeData, bind, Except.bind, he]
  rw [hback _ hm, hb]

end PyLean.TextLibs.Binascii
