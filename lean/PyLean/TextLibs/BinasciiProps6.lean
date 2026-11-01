import PyLean.TextLibs.BinasciiProps5

/-!
base32 and the multi-line interface. base32 packs five bytes into eight digits, and a short last group
leaves padding that the decoder turns back into a shift; `encodebytes` writes one base64 line per 57
bytes, and the lines join up because 57 is a multiple of 3.
-/

namespace PyLean.TextLibs.Binascii

open PyLean

set_option linter.unusedSimpArgs false

/-! ### base32: the encoder as a recursion -/

theorem b32Chunks_fuel (alpha : List Nat) : ∀ (f g : Nat) (l : List Nat), l.length ≤ f → l.length ≤ g →
    b32Chunks alpha f l = b32Chunks alpha g l := by
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
        simp only [b32Chunks]
        rw [ih g _ (by simp at h1 ⊢; omega) (by simp at h2 ⊢; omega)]

/-- The forty bits of five bytes. -/
def q5 (a b c d e : Nat) : Nat :=
  a * 4294967296 + b * 16777216 + c * 65536 + d * 256 + e

/-- The eight digits of a forty-bit group. -/
def digits8 (q : Nat) : List Nat :=
  [q / 2 ^ 30 / 32, q / 2 ^ 30 % 32, q / 2 ^ 20 % 1024 / 32, q / 2 ^ 20 % 1024 % 32,
   q / 2 ^ 10 % 1024 / 32, q / 2 ^ 10 % 1024 % 32, q % 1024 / 32, q % 1024 % 32]

/-- The characters of a group. -/
def group8 (alpha : List Nat) (q : Nat) : List Nat := (digits8 q).map fun v => alpha.getD v 0

theorem b32Chunks_step (alpha : List Nat) (f a b c d e : Nat) (r : List Nat) :
    b32Chunks alpha (f + 1) (a :: b :: c :: d :: e :: r) =
      group8 alpha (q5 a b c d e) ++ b32Chunks alpha f r := by
  have hq : (([a, b, c, d, e] : List Nat).foldl (fun x b => x * 256 + b) 0) = q5 a b c d e := by
    simp [q5]
    omega
  simp only [b32Chunks, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, hq]
  rfl

theorem group8_length (alpha : List Nat) (q : Nat) : (group8 alpha q).length = 8 := rfl

/-- `b32encode` as a recursion on five bytes at a time. -/
def b32R (alpha : List Nat) : List Nat → List Nat
  | a :: b :: c :: d :: e :: r => group8 alpha (q5 a b c d e) ++ b32R alpha r
  | [] => []
  | [a] => (group8 alpha (q5 a 0 0 0 0)).take 2 ++ List.replicate 6 61
  | [a, b] => (group8 alpha (q5 a b 0 0 0)).take 4 ++ List.replicate 4 61
  | [a, b, c] => (group8 alpha (q5 a b c 0 0)).take 5 ++ List.replicate 3 61
  | [a, b, c, d] => (group8 alpha (q5 a b c d 0)).take 7 ++ List.replicate 1 61

/-- How many `=` a length gives. -/
def padN (n : Nat) : Nat :=
  match n % 5 with
  | 1 => 6
  | 2 => 4
  | 3 => 3
  | 4 => 1
  | _ => 0

/-- Cutting the last digits of a stream of groups only touches the last group. -/
theorem take_group (X Y : List Nat) (n : Nat) (h : n ≤ Y.length) :
    (X ++ Y).take ((X ++ Y).length - n) = X ++ Y.take (Y.length - n) := by
  simp only [List.length_append]
  rw [show X.length + Y.length - n = X.length + (Y.length - n) by omega, List.take_append,
    List.take_of_length_le (by omega), Nat.add_sub_cancel_left]

theorem b32encode_eq (alpha s : List Nat) :
    b32encode alpha s =
      (let s' := if s.length % 5 ≠ 0 then s ++ List.replicate (5 - s.length % 5) 0 else s
       let encoded := b32Chunks alpha s'.length s'
       encoded.take (encoded.length - padN s.length) ++ List.replicate (padN s.length) 61) := rfl

theorem b32Chunks_len (alpha : List Nat) : ∀ (f : Nat) (l : List Nat), l.length ≤ f → l.length % 5 = 0 →
    (b32Chunks alpha f l).length = l.length / 5 * 8 := by
  intro f
  induction f with
  | zero =>
    intro l h _
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rfl
  | succ f ih =>
    intro l h h5
    match l, h, h5 with
    | [], _, _ => rfl
    | a :: b :: c :: d :: e :: r, h, h5 =>
      rw [b32Chunks_step, List.length_append, group8_length,
        ih r (by simp at h; omega) (by simp at h5; omega)]
      simp only [List.length_cons]
      omega
    | [a], _, h5 => simp at h5
    | [a, b], _, h5 => simp at h5
    | [a, b, c], _, h5 => simp at h5
    | [a, b, c, d], _, h5 => simp at h5

theorem padN_cons (n : Nat) : padN (n + 5) = padN n := by
  simp only [padN, Nat.add_mod_right]

theorem b32encode_rec (alpha : List Nat) : ∀ (n : Nat) (s : List Nat), s.length ≤ n →
    b32encode alpha s = b32R alpha s := by
  intro n
  induction n with
  | zero =>
    intro s h
    have : s = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rfl
  | succ n ih =>
    intro s h
    match s, h with
    | [], _ => rfl
    | [a], _ =>
      have hs : b32Chunks alpha 5 [a, 0, 0, 0, 0] = group8 alpha (q5 a 0 0 0 0) := by
        rw [b32Chunks_step]
        simp [b32Chunks]
      show (b32Chunks alpha 5 [a, 0, 0, 0, 0]).take ((b32Chunks alpha 5 [a, 0, 0, 0, 0]).length - 6) ++
        List.replicate 6 61 = _
      rw [hs, group8_length]
      rfl
    | [a, b], _ =>
      have hs : b32Chunks alpha 5 [a, b, 0, 0, 0] = group8 alpha (q5 a b 0 0 0) := by
        rw [b32Chunks_step]
        simp [b32Chunks]
      show (b32Chunks alpha 5 [a, b, 0, 0, 0]).take ((b32Chunks alpha 5 [a, b, 0, 0, 0]).length - 4) ++
        List.replicate 4 61 = _
      rw [hs, group8_length]
      rfl
    | [a, b, c], _ =>
      have hs : b32Chunks alpha 5 [a, b, c, 0, 0] = group8 alpha (q5 a b c 0 0) := by
        rw [b32Chunks_step]
        simp [b32Chunks]
      show (b32Chunks alpha 5 [a, b, c, 0, 0]).take ((b32Chunks alpha 5 [a, b, c, 0, 0]).length - 3) ++
        List.replicate 3 61 = _
      rw [hs, group8_length]
      rfl
    | [a, b, c, d], _ =>
      have hs : b32Chunks alpha 5 [a, b, c, d, 0] = group8 alpha (q5 a b c d 0) := by
        rw [b32Chunks_step]
        simp [b32Chunks]
      show (b32Chunks alpha 5 [a, b, c, d, 0]).take ((b32Chunks alpha 5 [a, b, c, d, 0]).length - 1) ++
        List.replicate 1 61 = _
      rw [hs, group8_length]
      rfl
    | a :: b :: c :: d :: e :: r, h =>
      have hi := ih r (by simp at h; omega)
      simp only [b32R]
      rw [← hi, b32encode_eq alpha (a :: b :: c :: d :: e :: r), b32encode_eq alpha r]
      have hl : (a :: b :: c :: d :: e :: r).length = r.length + 5 := rfl
      have hm : (r.length + 5) % 5 = r.length % 5 := by omega
      simp only [hl, hm, padN_cons]
      by_cases h0 : r.length % 5 ≠ 0
      · simp only [if_pos h0]
        generalize hk : List.replicate (5 - r.length % 5) 0 = k
        have hkl : k.length = 5 - r.length % 5 := by rw [← hk]; simp
        simp only [List.cons_append, List.length_cons]
        rw [b32Chunks_step]
        rw [b32Chunks_fuel alpha _ (r ++ k).length (r ++ k) (by omega) (by omega)]
        have hlen := b32Chunks_len alpha (r ++ k).length (r ++ k) (Nat.le_refl _)
          (by simp only [List.length_append]; omega)
        have hp : padN r.length ≤ (b32Chunks alpha (r ++ k).length (r ++ k)).length := by
          rw [hlen]
          simp only [List.length_append, padN]
          have : r.length + k.length ≥ 5 := by omega
          have h5 : (r.length + k.length) / 5 ≥ 1 := by omega
          split <;> omega
        rw [take_group _ _ _ hp]
        simp
      · have h0' : r.length % 5 = 0 := by omega
        have hp : padN r.length = 0 := by simp [padN, h0']
        simp only [hp, Nat.sub_zero, List.replicate_zero, List.append_nil, if_neg h0,
          List.length_cons]
        rw [b32Chunks_step, b32Chunks_fuel alpha _ r.length r (by omega) (by omega),
          List.take_length, List.take_length]

/-! ### base32: the decoder -/

/-- What the proof needs of an alphabet. -/
structure Alpha (alpha : List Nat) : Prop where
  rev : ∀ i, i < 32 → b32rev alpha (alpha.getD i 0) = some i
  ne : ∀ i, i < 32 → alpha.getD i 0 ≠ 61

theorem alpha_b32 : Alpha b32alphabet := ⟨by decide +kernel, by decide +kernel⟩
theorem alpha_b32hex : Alpha b32hexalphabet := ⟨by decide +kernel, by decide +kernel⟩

/-- The characters without the padding. -/
def body32 (alpha : List Nat) : List Nat → List Nat
  | a :: b :: c :: d :: e :: r => group8 alpha (q5 a b c d e) ++ body32 alpha r
  | [] => []
  | [a] => (group8 alpha (q5 a 0 0 0 0)).take 2
  | [a, b] => (group8 alpha (q5 a b 0 0 0)).take 4
  | [a, b, c] => (group8 alpha (q5 a b c 0 0)).take 5
  | [a, b, c, d] => (group8 alpha (q5 a b c d 0)).take 7

theorem b32R_eq (alpha : List Nat) : ∀ (n : Nat) (s : List Nat), s.length ≤ n →
    b32R alpha s = body32 alpha s ++ List.replicate (padN s.length) 61 := by
  intro n
  induction n with
  | zero =>
    intro s h
    have : s = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rfl
  | succ n ih =>
    intro s h
    match s, h with
    | [], _ => rfl
    | [a], _ => rfl
    | [a, b], _ => rfl
    | [a, b, c], _ => rfl
    | [a, b, c, d], _ => rfl
    | a :: b :: c :: d :: e :: r, h =>
      simp only [b32R, body32, List.append_assoc]
      rw [ih r (by simp at h; omega)]
      simp only [List.length_cons]
      rw [show r.length + 1 + 1 + 1 + 1 + 1 = r.length + 5 from rfl, padN_cons]

theorem digits8_lt (q : Nat) (h : q < 2 ^ 40) : ∀ v ∈ digits8 q, v < 32 := by
  intro v hv
  simp only [digits8, List.mem_cons, List.not_mem_nil, or_false] at hv
  omega

theorem group8_ne {alpha : List Nat} (ha : Alpha alpha) (q : Nat) (h : q < 2 ^ 40) :
    ∀ c ∈ group8 alpha q, c ≠ 61 := by
  intro c hc
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hc
  exact ha.ne v (digits8_lt q h v hv)

theorem q5_lt (a b c d e : Nat) (ha : a < 256) (hb : b < 256) (hc : c < 256) (hd : d < 256)
    (he : e < 256) : q5 a b c d e < 2 ^ 40 := by
  simp only [q5]
  omega

theorem body32_ne {alpha : List Nat} (ha : Alpha alpha) : ∀ (n : Nat) (s : List Nat), s.length ≤ n →
    (∀ x ∈ s, x < 256) → ∀ c ∈ body32 alpha s, c ≠ 61 := by
  intro n
  induction n with
  | zero =>
    intro s h _ c hc
    have : s = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [body32] at hc
  | succ n ih =>
    intro s h hb c hc
    match s, h, hb, hc with
    | [], _, _, hc => simp [body32] at hc
    | [a], _, hb, hc =>
      exact group8_ne ha _ (q5_lt _ _ _ _ _ (hb a (by simp)) (by omega) (by omega) (by omega) (by omega))
        c (List.mem_of_mem_take hc)
    | [a, b], _, hb, hc =>
      exact group8_ne ha _ (q5_lt _ _ _ _ _ (hb a (by simp)) (hb b (by simp)) (by omega) (by omega) (by omega))
        c (List.mem_of_mem_take hc)
    | [a, b, x], _, hb, hc =>
      exact group8_ne ha _ (q5_lt _ _ _ _ _ (hb a (by simp)) (hb b (by simp)) (hb x (by simp)) (by omega) (by omega))
        c (List.mem_of_mem_take hc)
    | [a, b, x, d], _, hb, hc =>
      exact group8_ne ha _ (q5_lt _ _ _ _ _ (hb a (by simp)) (hb b (by simp)) (hb x (by simp)) (hb d (by simp)) (by omega))
        c (List.mem_of_mem_take hc)
    | a :: b :: x :: d :: e :: r, h, hb, hc =>
      simp only [body32, List.mem_append] at hc
      rcases hc with hc | hc
      · exact group8_ne ha _ (q5_lt _ _ _ _ _ (hb a (by simp)) (hb b (by simp)) (hb x (by simp))
          (hb d (by simp)) (hb e (by simp))) c hc
      · exact ih r (by simp at h; omega) (fun y hy => hb y (by simp [hy])) c hc

theorem rstrip_pad (X : List Nat) (n : Nat) (h : ∀ c ∈ X, c ≠ 61) :
    rstripPad (X ++ List.replicate n 61) = X := by
  have hd : ∀ (m : Nat) (Y : List Nat), (∀ c ∈ Y, c ≠ 61) →
      (List.replicate m 61 ++ Y).dropWhile (· == 61) = Y := by
    intro m
    induction m with
    | zero =>
      intro Y hY
      cases Y with
      | nil => rfl
      | cons y t =>
        have : (y == 61) = false := beq_false_of_ne (hY y (by simp))
        simp [List.dropWhile, this]
    | succ m ih =>
      intro Y hY
      simp only [List.replicate_succ, List.cons_append, List.dropWhile_cons, beq_self_eq_true, if_true]
      exact ih Y hY
  unfold rstripPad
  rw [List.reverse_append, List.reverse_replicate, hd n X.reverse (by simpa using h),
    List.reverse_reverse]

theorem quanta_map {alpha : List Nat} (ha : Alpha alpha) : ∀ (ds : List Nat) (acc : Nat),
    (∀ v ∈ ds, v < 32) →
    b32Quanta alpha acc (ds.map fun v => alpha.getD v 0) =
      .ok (ds.foldl (fun x v => x * 32 + v) acc) := by
  intro ds
  induction ds with
  | nil => intro _ _; rfl
  | cons v r ih =>
    intro acc h
    simp only [List.map_cons, b32Quanta, ha.rev v (h v (by simp)), List.foldl_cons]
    exact ih _ (fun x hx => h x (by simp [hx]))

theorem digits_value (q : Nat) (h : q < 2 ^ 40) : (digits8 q).foldl (fun x v => x * 32 + v) 0 = q := by
  have e1 : q / 2 ^ 20 = q / 2 ^ 10 / 2 ^ 10 := by rw [Nat.div_div_eq_div_mul]
  have e2 : q / 2 ^ 30 = q / 2 ^ 10 / 2 ^ 10 / 2 ^ 10 := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  simp only [digits8, List.foldl_cons, List.foldl_nil]
  rw [e1, e2]
  generalize hx : q / 2 ^ 10 = x
  have hq : q = x * 1024 + q % 1024 := by omega
  generalize q % 1024 = l at *
  have hl : l < 1024 := by omega
  omega

theorem toBytes5_q5 (a b c d e : Nat) (ha : a < 256) (hb : b < 256) (hc : c < 256) (hd : d < 256)
    (he : e < 256) : toBytes5 (q5 a b c d e) = [a, b, c, d, e] := by
  simp only [toBytes5, q5, List.cons.injEq, and_true]
  omega

theorem decLoop_cons (alpha : List Nat) (f x : Nat) (t dec : List Nat) (acc : Nat) :
    b32DecLoop alpha (f + 1) (x :: t) dec acc =
      (b32Quanta alpha 0 ((x :: t).take 8) >>= fun a =>
        b32DecLoop alpha f ((x :: t).drop 8) (dec ++ toBytes5 a) a) := rfl

theorem decLoop_step {alpha : List Nat} (ha : Alpha alpha) (f : Nat) (q : Nat) (hq : q < 2 ^ 40)
    (rest dec : List Nat) (acc : Nat) :
    b32DecLoop alpha (f + 1) (group8 alpha q ++ rest) dec acc =
      b32DecLoop alpha f rest (dec ++ toBytes5 q) q := by
  have h8 : (group8 alpha q).length = 8 := rfl
  have ht : (group8 alpha q ++ rest).take 8 = group8 alpha q := by
    rw [List.take_append, List.take_of_length_le (by omega)]
    simp [h8]
  have hd : (group8 alpha q ++ rest).drop 8 = rest := by
    rw [List.drop_append]
    simp [h8]
  have hq2 : b32Quanta alpha 0 (group8 alpha q) = .ok q := by
    have := quanta_map ha (digits8 q) 0 (digits8_lt q hq)
    rw [digits_value q hq] at this
    exact this
  obtain ⟨x, t, hxt⟩ : ∃ x t, group8 alpha q ++ rest = x :: t := ⟨_, _, rfl⟩
  rw [hxt, decLoop_cons, ← hxt, ht, hd, hq2]
  rfl

/-- A short last group: everything in it is read, and the loop stops. -/
theorem decLoop_tail {alpha : List Nat} (ha : Alpha alpha) (f : Nat) (d : Nat) (ds : List Nat)
    (hv : ∀ v ∈ d :: ds, v < 32) (hl : (d :: ds).length ≤ 8) (dec : List Nat) (acc : Nat) :
    b32DecLoop alpha (f + 2) ((d :: ds).map fun v => alpha.getD v 0) dec acc =
      .ok (dec ++ toBytes5 ((d :: ds).foldl (fun x v => x * 32 + v) 0),
        (d :: ds).foldl (fun x v => x * 32 + v) 0) := by
  have hm : ((d :: ds).map fun v => alpha.getD v 0).length ≤ 8 := by simpa using hl
  have hq := quanta_map ha (d :: ds) 0 hv
  obtain ⟨x, t, hxt⟩ : ∃ x t, (d :: ds).map (fun v => alpha.getD v 0) = x :: t := ⟨_, _, rfl⟩
  rw [hxt, decLoop_cons, ← hxt, List.take_of_length_le hm, List.drop_of_length_le hm, hq]
  rfl

theorem take_map32 (alpha : List Nat) (q k : Nat) :
    (group8 alpha q).take k = ((digits8 q).take k).map fun v => alpha.getD v 0 := by
  simp [group8, List.map_take]

/-- A group in four ten-bit halves, which keeps the arithmetic small. -/
theorem digits8_of (q x y h3 h2 h1 h0 : Nat) (hy : y = h3 * 1024 + h2) (hx : x = y * 1024 + h1)
    (hq : q = x * 1024 + h0) (h2' : h2 < 1024) (h1' : h1 < 1024) (h0' : h0 < 1024) :
    digits8 q = [h3 / 32, h3 % 32, h2 / 32, h2 % 32, h1 / 32, h1 % 32, h0 / 32, h0 % 32] := by
  have e0 : q / 1024 = x := by omega
  have e1 : x / 1024 = y := by omega
  have e2 : y / 1024 = h3 := by omega
  have p10 : (2 : Nat) ^ 10 = 1024 := by decide
  have p20 : (2 : Nat) ^ 20 = 1024 * 1024 := by decide
  have p30 : (2 : Nat) ^ 30 = 1024 * 1024 * 1024 := by decide
  have e3 : q / 2 ^ 10 = x := by rw [p10, e0]
  have e4 : q / 2 ^ 20 = y := by rw [p20, ← Nat.div_div_eq_div_mul, e0, e1]
  have e5 : q / 2 ^ 30 = h3 := by
    rw [p30, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, e0, e1, e2]
  have e6 : q % 1024 = h0 := by omega
  have e7 : x % 1024 = h1 := by omega
  have e8 : y % 1024 = h2 := by omega
  simp only [digits8, e3, e4, e5, e6, e7, e8]

theorem q5_split (a b c d e : Nat) :
    q5 a b c d e = (((a * 4 + b / 64) * 1024 + (b % 64 * 16 + c / 16)) * 1024 +
      (c % 16 * 64 + d / 4)) * 1024 + (d % 4 * 256 + e) := by
  simp only [q5]
  omega

theorem digits8_q5 (a b c d e : Nat) (hc : c < 256) (hd : d < 256) (he : e < 256) :
    digits8 (q5 a b c d e) =
      [(a * 4 + b / 64) / 32, (a * 4 + b / 64) % 32,
       (b % 64 * 16 + c / 16) / 32, (b % 64 * 16 + c / 16) % 32,
       (c % 16 * 64 + d / 4) / 32, (c % 16 * 64 + d / 4) % 32,
       (d % 4 * 256 + e) / 32, (d % 4 * 256 + e) % 32] :=
  digits8_of _ _ _ _ _ _ _ rfl rfl (q5_split a b c d e) (by omega) (by omega) (by omega)

theorem tail_any_1 (a b c d e : Nat) (h1 : b = 0) (h2 : c = 0) (h3 : d = 0) (h4 : e = 0) :
    ((digits8 (q5 a b c d e)).take 2).foldl (fun x v => x * 32 + v) 0 = a * 4 := by
  rw [digits8_q5 _ _ _ _ _ (by omega) (by omega) (by omega)]
  simp only [List.take_succ_cons, List.take_zero, List.foldl_cons, List.foldl_nil]
  omega

theorem tail_any_2 (a b c d e : Nat) (hb : b < 256) (h2 : c = 0) (h3 : d = 0) (h4 : e = 0) :
    ((digits8 (q5 a b c d e)).take 4).foldl (fun x v => x * 32 + v) 0 = a * 4096 + b * 16 := by
  rw [digits8_q5 _ _ _ _ _ (by omega) (by omega) (by omega)]
  simp only [List.take_succ_cons, List.take_zero, List.foldl_cons, List.foldl_nil]
  omega

theorem tail_any_3 (a b c d e : Nat) (hb : b < 256) (hc : c < 256) (h3 : d = 0) (h4 : e = 0) :
    ((digits8 (q5 a b c d e)).take 5).foldl (fun x v => x * 32 + v) 0 =
      a * 131072 + b * 512 + c * 2 := by
  rw [digits8_q5 _ _ _ _ _ (by omega) (by omega) (by omega)]
  simp only [List.take_succ_cons, List.take_zero, List.foldl_cons, List.foldl_nil]
  omega

theorem tail_any_4 (a b c d e : Nat) (hb : b < 256) (hc : c < 256) (hd : d < 256) (h4 : e = 0) :
    ((digits8 (q5 a b c d e)).take 7).foldl (fun x v => x * 32 + v) 0 =
      a * 134217728 + b * 524288 + c * 2048 + d * 8 := by
  rw [digits8_q5 _ _ _ _ _ (by omega) (by omega) (by omega)]
  simp only [List.take_succ_cons, List.take_zero, List.foldl_cons, List.foldl_nil]
  omega

/-- What the decoder's loop must leave. -/
def Fin32 (s out : List Nat) (acc : Nat) : Prop :=
  (padN s.length = 0 → out = s) ∧
  (padN s.length ≠ 0 → 5 ≤ out.length ∧
    out.take (out.length - 5) ++
      (toBytes5 (acc * 2 ^ (5 * padN s.length))).take ((43 - 5 * padN s.length) / 8) = s)

theorem dec_go {alpha : List Nat} (ha : Alpha alpha) : ∀ (n : Nat) (s : List Nat), s.length ≤ n →
    (∀ x ∈ s, x < 256) → ∀ (dec : List Nat) (acc f : Nat), (body32 alpha s).length + 1 ≤ f →
    ∃ out acc', b32DecLoop alpha f (body32 alpha s) dec acc = .ok (dec ++ out, acc') ∧
      Fin32 s out acc' := by
  intro n
  induction n with
  | zero =>
    intro s h _ dec acc f hf
    have : s = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [body32] at hf; omega⟩
    exact ⟨[], acc, by simp [body32, b32DecLoop], by simp [Fin32, padN]⟩
  | succ n ih =>
    intro s h hb dec acc f hf
    have hd8 : ∀ q, q < 2 ^ 40 → ∀ k, ∀ v ∈ (digits8 q).take k, v < 32 :=
      fun q hq k v hv => digits8_lt q hq v (List.mem_of_mem_take hv)
    match s, h, hb, hf with
    | [], _, _, hf =>
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [body32] at hf; omega⟩
      exact ⟨[], acc, by simp [body32, b32DecLoop], by simp [Fin32, padN]⟩
    | [a], _, hb, hf =>
      have ha' : a < 256 := hb a (by simp)
      have hq := q5_lt a 0 0 0 0 ha' (by omega) (by omega) (by omega) (by omega)
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by
        have : (body32 alpha [a]).length = 2 := rfl
        omega⟩
      have hl : body32 alpha [a] = ((digits8 (q5 a 0 0 0 0)).take 2).map fun v => alpha.getD v 0 :=
        take_map32 _ _ _
      obtain ⟨d1, ds, hds⟩ : ∃ d ds, (digits8 (q5 a 0 0 0 0)).take 2 = d :: ds := ⟨_, _, rfl⟩
      have hv1 := tail_any_1 a 0 0 0 0 rfl rfl rfl rfl
      rw [hds] at hl hv1
      have hv := hd8 _ hq 2
      rw [hds] at hv
      refine ⟨toBytes5 (a * 4), a * 4, ?_, by simp [padN], ?_⟩
      · rw [hl, decLoop_tail ha g d1 ds hv (by rw [← hds]; simp [digits8]), hv1]
      · intro _
        refine ⟨by simp [toBytes5], ?_⟩
        simp only [toBytes5, padN, List.length_cons, List.length_nil]
        simp
        omega
    | [a, b], _, hb, hf =>
      have ha' : a < 256 := hb a (by simp)
      have hb' : b < 256 := hb b (by simp)
      have hq := q5_lt a b 0 0 0 ha' hb' (by omega) (by omega) (by omega)
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by
        have : (body32 alpha [a, b]).length = 4 := rfl
        omega⟩
      have hl : body32 alpha [a, b] = ((digits8 (q5 a b 0 0 0)).take 4).map fun v => alpha.getD v 0 :=
        take_map32 _ _ _
      obtain ⟨d1, ds, hds⟩ : ∃ d ds, (digits8 (q5 a b 0 0 0)).take 4 = d :: ds := ⟨_, _, rfl⟩
      have hv1 := tail_any_2 a b 0 0 0 hb' rfl rfl rfl
      rw [hds] at hl hv1
      have hv := hd8 _ hq 4
      rw [hds] at hv
      refine ⟨toBytes5 (a * 4096 + b * 16), a * 4096 + b * 16, ?_, by simp [padN], ?_⟩
      · rw [hl, decLoop_tail ha g d1 ds hv (by rw [← hds]; simp [digits8]), hv1]
      · intro _
        refine ⟨by simp [toBytes5], ?_⟩
        simp only [toBytes5, padN, List.length_cons, List.length_nil]
        simp
        omega
    | [a, b, c], _, hb, hf =>
      have ha' : a < 256 := hb a (by simp)
      have hb' : b < 256 := hb b (by simp)
      have hc : c < 256 := hb c (by simp)
      have hq := q5_lt a b c 0 0 ha' hb' hc (by omega) (by omega)
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by
        have : (body32 alpha [a, b, c]).length = 5 := rfl
        omega⟩
      have hl : body32 alpha [a, b, c] = ((digits8 (q5 a b c 0 0)).take 5).map fun v => alpha.getD v 0 :=
        take_map32 _ _ _
      obtain ⟨d1, ds, hds⟩ : ∃ d ds, (digits8 (q5 a b c 0 0)).take 5 = d :: ds := ⟨_, _, rfl⟩
      have hv1 := tail_any_3 a b c 0 0 hb' hc rfl rfl
      rw [hds] at hl hv1
      have hv := hd8 _ hq 5
      rw [hds] at hv
      refine ⟨toBytes5 (a * 131072 + b * 512 + c * 2), a * 131072 + b * 512 + c * 2, ?_, by simp [padN], ?_⟩
      · rw [hl, decLoop_tail ha g d1 ds hv (by rw [← hds]; simp [digits8]), hv1]
      · intro _
        refine ⟨by simp [toBytes5], ?_⟩
        simp only [toBytes5, padN, List.length_cons, List.length_nil]
        simp
        omega
    | [a, b, c, d], _, hb, hf =>
      have ha' : a < 256 := hb a (by simp)
      have hb' : b < 256 := hb b (by simp)
      have hc : c < 256 := hb c (by simp)
      have hd : d < 256 := hb d (by simp)
      have hq := q5_lt a b c d 0 ha' hb' hc hd (by omega)
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by
        have : (body32 alpha [a, b, c, d]).length = 7 := rfl
        omega⟩
      have hl : body32 alpha [a, b, c, d] =
          ((digits8 (q5 a b c d 0)).take 7).map fun v => alpha.getD v 0 := take_map32 _ _ _
      obtain ⟨d1, ds, hds⟩ : ∃ x ds, (digits8 (q5 a b c d 0)).take 7 = x :: ds := ⟨_, _, rfl⟩
      have hv1 := tail_any_4 a b c d 0 hb' hc hd rfl
      rw [hds] at hl hv1
      have hv := hd8 _ hq 7
      rw [hds] at hv
      refine ⟨toBytes5 (a * 134217728 + b * 524288 + c * 2048 + d * 8),
        a * 134217728 + b * 524288 + c * 2048 + d * 8, ?_, by simp [padN], ?_⟩
      · rw [hl, decLoop_tail ha g d1 ds hv (by rw [← hds]; simp [digits8]), hv1]
      · intro _
        refine ⟨by simp [toBytes5], ?_⟩
        simp only [toBytes5, padN, List.length_cons, List.length_nil]
        simp
        omega
    | a :: b :: c :: d :: e :: r, h, hb, hf =>
      have ha' : a < 256 := hb a (by simp)
      have hb' : b < 256 := hb b (by simp)
      have hc : c < 256 := hb c (by simp)
      have hd : d < 256 := hb d (by simp)
      have he : e < 256 := hb e (by simp)
      have hq := q5_lt a b c d e ha' hb' hc hd he
      simp only [body32, List.length_append, group8_length] at hf ⊢
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      rw [decLoop_step ha g _ hq, toBytes5_q5 a b c d e ha' hb' hc hd he]
      obtain ⟨out, acc', h1, h2, h3⟩ := ih r (by simp at h; omega) (fun x hx => hb x (by simp [hx]))
        (dec ++ [a, b, c, d, e]) (q5 a b c d e) g (by omega)
      have hp : padN (a :: b :: c :: d :: e :: r).length = padN r.length := padN_cons r.length
      refine ⟨[a, b, c, d, e] ++ out, acc', by rw [h1]; simp, fun h0 => ?_, fun h0 => ?_⟩
      · rw [hp] at h0
        rw [h2 h0]
        rfl
      · rw [hp] at h0 ⊢
        obtain ⟨h4, h5⟩ := h3 h0
        refine ⟨by simp only [List.length_append]; omega, ?_⟩
        rw [take_group _ _ _ h4, List.append_assoc, h5]
        rfl

theorem body32_length (alpha : List Nat) : ∀ (n : Nat) (s : List Nat), s.length ≤ n →
    ((body32 alpha s).length + padN s.length) % 8 = 0 := by
  intro n
  induction n with
  | zero =>
    intro s h
    have : s = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rfl
  | succ n ih =>
    intro s h
    match s, h with
    | [], _ => rfl
    | [a], _ =>
      rw [show (body32 alpha [a]).length = 2 from rfl]
      simp [padN]
    | [a, b], _ =>
      rw [show (body32 alpha [a, b]).length = 4 from rfl]
      simp [padN]
    | [a, b, c], _ =>
      rw [show (body32 alpha [a, b, c]).length = 5 from rfl]
      simp [padN]
    | [a, b, c, d], _ =>
      rw [show (body32 alpha [a, b, c, d]).length = 7 from rfl]
      simp [padN]
    | a :: b :: c :: d :: e :: r, h =>
      have := ih r (by simp at h; omega)
      have hp : padN (a :: b :: c :: d :: e :: r).length = padN r.length := padN_cons r.length
      simp only [body32, hp, List.length_append, group8_length]
      omega

theorem padN_mem (n : Nat) : [0, 1, 3, 4, 6].contains (padN n) = true := by
  simp only [padN]
  split <;> decide

/-- `b32decode(b32encode(d)) == d`, and the same for `b32hexencode`, for every number of bytes, so
through all four padding lengths. -/
def B32RoundTrip : Prop :=
  ∀ (alpha d : List Nat), (alpha = b32alphabet ∨ alpha = b32hexalphabet) → (∀ x ∈ d, x < 256) →
    b32decode alpha (.bytes (b32encode alpha d)) false none = .ok d

theorem b32RoundTrip_proven : B32RoundTrip := by
  intro alpha d hA hd
  have ha : Alpha alpha := by
    rcases hA with h | h
    · rw [h]
      exact alpha_b32
    · rw [h]
      exact alpha_b32hex
  rw [b32encode_rec alpha d.length d (Nat.le_refl _), b32R_eq alpha d.length d (Nat.le_refl _)]
  have hne := body32_ne ha d.length d (Nat.le_refl _) hd
  have hlen := body32_length alpha d.length d (Nat.le_refl _)
  obtain ⟨out, acc', h1, h2, h3⟩ := dec_go ha d.length d (Nat.le_refl _) hd [] 0
    ((body32 alpha d).length + 1) (Nat.le_refl _)
  generalize hB : body32 alpha d = B at *
  generalize hP : padN d.length = P at *
  have hs : rstripPad (B ++ List.replicate P 61) = B := rstrip_pad B P hne
  have hl : (B ++ List.replicate P 61).length = B.length + P := by simp
  have hl8 : ¬(B ++ List.replicate P 61).length % 8 ≠ 0 := by
    rw [hl]
    omega
  have hpc : [0, 1, 3, 4, 6].contains P = true := by
    rw [← hP]
    exact padN_mem _
  simp only [b32decode, bytesFromDecodeData, bind, Except.bind, pure, Except.pure]
  rw [if_neg hl8]
  simp only [Bool.false_eq_true, if_false, hs, hl]
  rw [show B.length + P - B.length = P by omega, h1]
  simp only [List.nil_append]
  have hl9 : (B.length + P) % 8 = 0 := by omega
  rw [if_neg (fun h => h.elim (fun h => h (by simpa using hl9))
    (fun h => by rw [hpc] at h; exact absurd h (by decide)))]
  by_cases h0 : P = 0
  · subst h0
    rw [if_neg (by simp)]
    rw [h2 rfl]
  · obtain ⟨h4, h5⟩ := h3 h0
    have hn : out.isEmpty = false := by
      apply List.isEmpty_eq_false_iff.2
      intro h6
      rw [h6] at h4
      simp at h4
    rw [if_pos ⟨h0, by simp [hn]⟩]
    rw [h5]

end PyLean.TextLibs.Binascii
