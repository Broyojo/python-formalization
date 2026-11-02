import PyLean.TextLibs.BinasciiEq2
import PyLean.TextLibs.BinasciiTables

/-!
The round trips of base32, base85 and Ascii85, which 3.15 moved into `Modules/binascii.c`.
-/

namespace PyLean.TextLibs.Binascii

open PyLean

/-- `b32decode`'s two options rewrite the input before anything is decoded, `map01` first: with
`casefold`, a `map01` of `b'l'` still reads as `L`. A `map01` of any other length is refused by
`bytes.maketrans`. -/
def B32OptionLawC : Prop :=
  ∀ (s m ig : List Nat) (p c : Bool),
    (m.length = 1 → pyB32decode (.bytes s) true (some (.bytes m)) p (.bytes ig) c =
      pyB32decode (.bytes (upper (translate [48, 49] (79 :: m) s))) false none p (.bytes ig) c) ∧
    (m.length ≠ 1 → pyB32decode (.bytes s) true (some (.bytes m)) p (.bytes ig) c =
      .error (.valueError "maketrans arguments must have same length"))

theorem b32OptionLawC_proven : B32OptionLawC := by
  intro s m ig p c
  constructor
  · intro h
    simp [pyB32decode, bytesFromDecodeData, h, bind, Except.bind, pure, Except.pure]
  · intro h
    simp [pyB32decode, bytesFromDecodeData, h, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExcept.throw,
      MonadExceptOf.throw]

/-! ### `get_reverse_table` -/

theorem find_rev : ∀ (a : List Nat) (k i : Nat), a.Nodup → i < a.length →
    ((a.zipIdx k).reverse.find? (·.1 == a.getD i 0)).map (·.2) = some (k + i) := by
  intro a
  induction a with
  | nil => intro _ _ _ h; simp at h
  | cons x r ih =>
    intro k i hn hi
    have hx : x ∉ r := (List.nodup_cons.mp hn).1
    have hr : r.Nodup := (List.nodup_cons.mp hn).2
    simp only [List.zipIdx_cons, List.reverse_cons, List.find?_append]
    cases i with
    | zero =>
      have hnone : (r.zipIdx (k + 1)).reverse.find? (·.1 == (x :: r).getD 0 0) = none := by
        apply List.find?_eq_none.mpr
        intro y hy
        have hm : y ∈ r.zipIdx (k + 1) := List.mem_reverse.mp hy
        have h1 : y.1 ∈ r := List.fst_mem_of_mem_zipIdx hm
        have h2 : y.1 ≠ x := fun e => hx (e ▸ h1)
        simpa using h2
      rw [hnone]
      simp
    | succ j =>
      have hj : j < r.length := by simpa using hi
      have h := ih (k + 1) j hr hj
      have e : (x :: r).getD (j + 1) 0 = r.getD j 0 := by simp
      rw [e]
      cases hf : (r.zipIdx (k + 1)).reverse.find? (·.1 == r.getD j 0) with
      | none =>
        rw [hf] at h
        simp at h
      | some y =>
        rw [hf] at h
        simp only [Option.map_some, Option.some.injEq] at h
        simp only [Option.some_or, Option.map_some, Option.some.injEq, h]
        omega

/-- The table `get_reverse_table` builds inverts an alphabet of distinct bytes, where the padding
character is not the character in question. -/
theorem revT_index (a : List Nat) (p : Option Nat) (i : Nat) (hn : a.Nodup) (hi : i < a.length)
    (hp : p ≠ some (a.getD i 0)) : revT a p (a.getD i 0) = i := by
  have h1 : (p == some (a.getD i 0)) = false := by simpa using hp
  have h2 := find_rev a 0 i hn hi
  have e : a.zipIdx = a.zipIdx 0 := rfl
  simp only [revT, h1, Bool.false_eq_true, if_false, e, h2]
  simp

/-- The padding character maps to the size of the alphabet, whatever the alphabet holds. -/
theorem revT_pad (a : List Nat) (c : Nat) : revT a (some c) c = a.length := by
  simp [revT]

/-! ### base32 -/

theorem dec32_octa (st : Dec32) (v : Nat) (h : st.octa < 7) : (decStep32 st v).octa = st.octa + 1 := by
  obtain ⟨o, p, l, r⟩ := st
  simp only at h
  match o, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ => rfl

theorem dec32_pads (st : Dec32) (v : Nat) : (decStep32 st v).pads = st.pads := by
  obtain ⟨o, p, l, r⟩ := st
  simp only [decStep32]
  split <;> rfl

/-- A data character, not at the last place of a group. -/
theorem run32_d (t : Nat → Nat) (x v f : Nat) (xs : List Nat) (st : Dec32) (hx : x ≠ 61) (hv : t x = v) (h32 : v < 32)
    (hp : st.pads = 0) (h7 : st.octa ≠ 7) :
    a2b32Run t true none (f + 1) (x :: xs) st = a2b32Run t true none f xs (decStep32 st v) := by
  have h1 : (x == 61) = false := by simpa using hx
  have h2 : ¬ v ≥ 32 := by omega
  simp only [a2b32Run, Bool.true_and, h1, Bool.false_eq_true, if_false, hv, h2, hp, h7]
  simp

/-- A run of data characters. -/
theorem run32_ds (a : List Nat) (t : Nat → Nat) (ht : ∀ v, v < 32 → t (a.getD v 0) = v)
    (hn : ∀ v, v < 32 → a.getD v 0 ≠ 61) :
    ∀ (vs : List Nat) (st : Dec32) (f : Nat) (rest : List Nat), (∀ v ∈ vs, v < 32) → st.pads = 0 →
      st.octa + vs.length ≤ 7 →
      a2b32Run t true none (f + vs.length) (vs.map (a.getD · 0) ++ rest) st =
        a2b32Run t true none f rest (vs.foldl decStep32 st) := by
  intro vs
  induction vs with
  | nil => intro _ _ _ _ _ _; rfl
  | cons v r ih =>
    intro st f rest hv hp ho
    have hl : v < 32 := hv v (by simp)
    simp only [List.length_cons] at ho
    have e : f + (v :: r).length = (f + r.length) + 1 := by simp; omega
    rw [e, List.map_cons, List.cons_append, run32_d t _ v _ _ st (hn v hl) (ht v hl) hl hp (by omega),
      ih _ f rest (fun y hy => hv y (by simp [hy])) (by rw [dec32_pads, hp]) (by rw [dec32_octa _ _ (by omega)]; omega)]
    rfl

/-- The padding of a cut group. -/
theorem run32_ps (t : Nat → Nat) : ∀ (n : Nat) (st : Dec32) (f : Nat),
    (st.octa = 2 ∨ st.octa = 4 ∨ st.octa = 5 ∨ st.octa = 7) → st.octa + st.pads + n ≤ 8 →
    a2b32Run t true none (f + n + 1) (List.replicate n 61) st = .ok { st with pads := st.pads + n } := by
  intro n
  induction n with
  | zero =>
    intro st f _ _
    simp [a2b32Run]
  | succ n ih =>
    intro st f ho hp
    have e : f + (n + 1) + 1 = (f + n + 1) + 1 := by omega
    have hc : (st.octa == 2 || st.octa == 4 || st.octa == 5 || st.octa == 7) = true := by
      rcases ho with h | h | h | h <;> simp [h]
    have hd : st.octa + (st.pads + 1) ≤ 8 := by omega
    rw [e, List.replicate_succ]
    simp only [a2b32Run, Bool.true_and, beq_self_eq_true, if_true, hc, decide_true, hd]
    have := ih { st with pads := st.pads + 1 } f ho (by simp only; omega)
    simp only [Bool.and_true, decide_eq_true_eq] at this ⊢
    have e2 : st.pads + 1 + n = st.pads + (n + 1) := by omega
    rw [this, e2]

/-- A group that holds padding is left to the slow path. -/
theorem fast32_stop (t : Nat → Nat) (h61 : 32 ≤ t 61) (k : Nat) (s out : List Nat) (hl : s.length = 8) (hm : 61 ∈ s) :
    fast32 t (k + 1) s out = (s, out) := by
  have ht : s.take 8 = s := List.take_of_length_le (by omega)
  have ha : (s.map t).any (· ≥ 32) = true := by
    apply List.any_eq_true.mpr
    exact ⟨t 61, List.mem_map.mpr ⟨61, hm, rfl⟩, by simpa using h61⟩
  simp only [fast32, hl, ge_iff_le, Nat.le_refl, if_true, octa32, ht, ha]

/-- Reading a whole encoded input: the data of `d` after `out`, and nothing left to complain about. -/
def Done32 (st : Dec32) (want : List Nat) : Prop :=
  st.out = want ∧ st.octa ≠ 1 ∧ st.octa ≠ 3 ∧ st.octa ≠ 6 ∧ (st.octa = 0 ∨ st.octa + st.pads = 8)

/-- The short fast path of the encoder does nothing. -/
theorem fe32_short (a d : List Nat) (f : Nat) (h : d.length < 5) : fastEnc32 a f d = ([], d) := by
  cases f with
  | zero => rfl
  | succ f =>
    simp only [fastEnc32]
    rw [if_neg (by omega)]

/-- The whole of a cut last group goes through the slow loop. -/
theorem tail32_run (a : List Nat) (t : Nat → Nat) (ht : ∀ v, v < 32 → t (a.getD v 0) = v)
    (hn : ∀ v, v < 32 → a.getD v 0 ≠ 61) (h61 : 32 ≤ t 61) (vs : List Nat) (n ff fr : Nat) (out : List Nat)
    (hv : ∀ v ∈ vs, v < 32) (h8 : vs.length + n = 8) (hn0 : n ≠ 0)
    (hk : vs.length = 2 ∨ vs.length = 4 ∨ vs.length = 5 ∨ vs.length = 7) (hff : 8 ≤ ff) (hfr : 8 < fr) :
    a2b32Run t true none fr (fast32 t ff (vs.map (a.getD · 0) ++ List.replicate n 61) out).1
        { out := (fast32 t ff (vs.map (a.getD · 0) ++ List.replicate n 61) out).2 } =
      .ok { (vs.foldl decStep32 ({ out := out } : Dec32)) with pads := n } := by
  obtain ⟨k, rfl⟩ : ∃ k, ff = k + 1 := ⟨ff - 1, by omega⟩
  have hs : (vs.map (a.getD · 0) ++ List.replicate n 61).length = 8 := by simpa using h8
  have hm : 61 ∈ vs.map (a.getD · 0) ++ List.replicate n 61 := by
    apply List.mem_append_right
    exact List.mem_replicate.mpr ⟨hn0, rfl⟩
  rw [fast32_stop t h61 k _ out hs hm]
  obtain ⟨g, rfl⟩ : ∃ g, fr = g + n + 1 + vs.length := ⟨fr - 1 - n - vs.length, by omega⟩
  simp only
  rw [run32_ds a t ht hn vs _ _ _ hv rfl (by simp only; omega)]
  have ho : ∀ (r : List Nat) (st : Dec32), st.octa + r.length ≤ 7 → (r.foldl decStep32 st).octa = st.octa + r.length := by
    intro r
    induction r with
    | nil => intro _ _; rfl
    | cons x r ih =>
      intro st h
      simp only [List.length_cons] at h
      simp only [List.foldl_cons, List.length_cons]
      rw [ih _ (by rw [dec32_octa _ _ (by omega)]; omega), dec32_octa _ _ (by omega)]
      omega
  have hp : ∀ (r : List Nat) (st : Dec32), (r.foldl decStep32 st).pads = st.pads := by
    intro r
    induction r with
    | nil => intro _; rfl
    | cons x r ih =>
      intro st
      simp only [List.foldl_cons]
      rw [ih, dec32_pads]
  have h1 := ho vs { out := out } (by simp only; omega)
  simp only [Nat.zero_add] at h1
  have h2 := hp vs { out := out }
  rw [run32_ps t n _ g (by rw [h1]; simpa using hk) (by rw [h1, h2]; simp only; omega)]
  rw [h2]
  simp

/-- What `binascii_b2a_base32_impl` writes, with `fe` as the fuel of its fast path. -/
def enc32S (a : List Nat) (fe : Nat) (d : List Nat) : List Nat :=
  (fastEnc32 a fe d).1 ++ tail32 a (fastEnc32 a fe d).2 ++ List.replicate ((5 - d.length % 5) % 5 * 8 / 5) 61

theorem enc32S_nil (a : List Nat) (fe : Nat) : enc32S a fe [] = [] := by
  unfold enc32S
  rw [fe32_short a [] fe (by simp)]
  rfl

theorem enc32S_1 (a : List Nat) (fe x : Nat) :
    enc32S a fe [x] = [x / 2 ^ 3 % 32, x * 4 % 32].map (a.getD · 0) ++ List.replicate 6 61 := by
  unfold enc32S
  rw [fe32_short a [x] fe (by simp)]
  simp [tail32]

theorem enc32S_2 (a : List Nat) (fe x y : Nat) :
    enc32S a fe [x, y] = [(x * 256 + y) / 2 ^ 11 % 32, (x * 256 + y) / 2 ^ 6 % 32, (x * 256 + y) / 2 ^ 1 % 32,
      (x * 256 + y) * 16 % 32].map (a.getD · 0) ++ List.replicate 4 61 := by
  unfold enc32S
  rw [fe32_short a [x, y] fe (by simp)]
  simp [tail32]

theorem enc32S_3 (a : List Nat) (fe x y z : Nat) :
    enc32S a fe [x, y, z] =
      [(x * 65536 + y * 256 + z) / 2 ^ 19 % 32, (x * 65536 + y * 256 + z) / 2 ^ 14 % 32,
       (x * 65536 + y * 256 + z) / 2 ^ 9 % 32, (x * 65536 + y * 256 + z) / 2 ^ 4 % 32,
       (x * 65536 + y * 256 + z) * 2 % 32].map (a.getD · 0) ++ List.replicate 3 61 := by
  unfold enc32S
  rw [fe32_short a [x, y, z] fe (by simp)]
  simp [tail32]

theorem enc32S_4 (a : List Nat) (fe x y z w : Nat) :
    enc32S a fe [x, y, z, w] =
      [(x * 16777216 + y * 65536 + z * 256 + w) / 2 ^ 27 % 32, (x * 16777216 + y * 65536 + z * 256 + w) / 2 ^ 22 % 32,
       (x * 16777216 + y * 65536 + z * 256 + w) / 2 ^ 17 % 32, (x * 16777216 + y * 65536 + z * 256 + w) / 2 ^ 12 % 32,
       (x * 16777216 + y * 65536 + z * 256 + w) / 2 ^ 7 % 32, (x * 16777216 + y * 65536 + z * 256 + w) / 2 ^ 2 % 32,
       (x * 16777216 + y * 65536 + z * 256 + w) * 8 % 32].map (a.getD · 0) ++ List.replicate 1 61 := by
  unfold enc32S
  rw [fe32_short a [x, y, z, w] fe (by simp)]
  simp [tail32]

theorem t1 (x : Nat) : x / 2 ^ 3 % 32 = x / 8 % 32 ∧ x * 4 % 32 = x % 8 * 4 := by
  constructor <;> omega

theorem t2 (x y : Nat) (hx : x < 256) (hy : y < 256) :
    (x * 256 + y) / 2 ^ 11 % 32 = x / 8 ∧ (x * 256 + y) / 2 ^ 6 % 32 = x % 8 * 4 + y / 64 ∧
      (x * 256 + y) / 2 ^ 1 % 32 = y / 2 % 32 ∧ (x * 256 + y) * 16 % 32 = y % 2 * 16 := by
  refine ⟨by omega, by omega, by omega, by omega⟩

theorem t3 (x y z : Nat) (hx : x < 256) (hy : y < 256) (hz : z < 256) :
    (x * 65536 + y * 256 + z) / 2 ^ 19 % 32 = x / 8 ∧ (x * 65536 + y * 256 + z) / 2 ^ 14 % 32 = x % 8 * 4 + y / 64 ∧
      (x * 65536 + y * 256 + z) / 2 ^ 9 % 32 = y / 2 % 32 ∧
      (x * 65536 + y * 256 + z) / 2 ^ 4 % 32 = y % 2 * 16 + z / 16 ∧
      (x * 65536 + y * 256 + z) * 2 % 32 = z % 16 * 2 := by
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem t4 (x y z w : Nat) (hx : x < 256) (hy : y < 256) (hz : z < 256) (hw : w < 256) :
    (x * 16777216 + y * 65536 + z * 256 + w) / 2 ^ 27 % 32 = x / 8 ∧
      (x * 16777216 + y * 65536 + z * 256 + w) / 2 ^ 22 % 32 = x % 8 * 4 + y / 64 ∧
      (x * 16777216 + y * 65536 + z * 256 + w) / 2 ^ 17 % 32 = y / 2 % 32 ∧
      (x * 16777216 + y * 65536 + z * 256 + w) / 2 ^ 12 % 32 = y % 2 * 16 + z / 16 ∧
      (x * 16777216 + y * 65536 + z * 256 + w) / 2 ^ 7 % 32 = z % 16 * 2 + w / 128 ∧
      (x * 16777216 + y * 65536 + z * 256 + w) / 2 ^ 2 % 32 = w / 4 % 32 ∧
      (x * 16777216 + y * 65536 + z * 256 + w) * 8 % 32 = w % 4 * 8 := by
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem t5 (x1 x2 x3 x4 x5 V : Nat) (b1 : x1 < 256) (b2 : x2 < 256) (b3 : x3 < 256) (b4 : x4 < 256) (b5 : x5 < 256)
    (hV : V = x1 * 2 ^ 32 + x2 * 2 ^ 24 + x3 * 65536 + x4 * 256 + x5) :
    V / 2 ^ 35 % 32 = x1 / 8 ∧ V / 2 ^ 30 % 32 = x1 % 8 * 4 + x2 / 64 ∧ V / 2 ^ 25 % 32 = x2 / 2 % 32 ∧
      V / 2 ^ 20 % 32 = x2 % 2 * 16 + x3 / 16 ∧ V / 2 ^ 15 % 32 = x3 % 16 * 2 + x4 / 128 ∧
      V / 2 ^ 10 % 32 = x4 / 4 % 32 ∧ V / 2 ^ 5 % 32 = x4 % 4 * 8 + x5 / 32 ∧ V / 2 ^ 0 % 32 = x5 % 32 := by
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem bytes5 (x1 x2 x3 x4 x5 : Nat) (b1 : x1 < 256) (b2 : x2 < 256) (b3 : x3 < 256) (b4 : x4 < 256) (b5 : x5 < 256) :
    [((x1 / 8) * 8 + (x1 % 8 * 4 + x2 / 64) / 4) % 256,
     ((x1 % 8 * 4 + x2 / 64) * 64 + (x2 / 2 % 32) * 2 + (x2 % 2 * 16 + x3 / 16) / 16) % 256,
     ((x2 % 2 * 16 + x3 / 16) * 16 + (x3 % 16 * 2 + x4 / 128) / 2) % 256,
     ((x3 % 16 * 2 + x4 / 128) * 128 + (x4 / 4 % 32) * 4 + (x4 % 4 * 8 + x5 / 32) / 8) % 256,
     ((x4 % 4 * 8 + x5 / 32) * 32 + x5 % 32) % 256] = [x1, x2, x3, x4, x5] := by
  simp only [List.cons.injEq, and_true]
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem enc32S_5 (a : List Nat) (fe x1 x2 x3 x4 x5 : Nat) (r : List Nat) (V : Nat)
    (hV : V = x1 * 2 ^ 32 + x2 * 2 ^ 24 + x3 * 65536 + x4 * 256 + x5) :
    enc32S a (fe + 1) (x1 :: x2 :: x3 :: x4 :: x5 :: r) =
      [V / 2 ^ 35 % 32, V / 2 ^ 30 % 32, V / 2 ^ 25 % 32, V / 2 ^ 20 % 32, V / 2 ^ 15 % 32, V / 2 ^ 10 % 32,
       V / 2 ^ 5 % 32, V / 2 ^ 0 % 32].map (a.getD · 0) ++ enc32S a fe r := by
  have ht : (x1 :: x2 :: x3 :: x4 :: x5 :: r).take 5 = [x1, x2, x3, x4, x5] := rfl
  have hd : (x1 :: x2 :: x3 :: x4 :: x5 :: r).drop 5 = r := rfl
  have hc : fastEnc32 a (fe + 1) (x1 :: x2 :: x3 :: x4 :: x5 :: r) =
      ((List.range 8).map (fun i => a.getD (V / 2 ^ (35 - 5 * i) % 32) 0) ++ (fastEnc32 a fe r).1,
        (fastEnc32 a fe r).2) := by
    rw [fastEnc32, if_pos (by simp only [List.length_cons]; omega)]
    simp only [ht, hd, List.foldl_cons, List.foldl_nil]
    have hv : (((((0 * 256 + x1) * 256 + x2) * 256 + x3) * 256 + x4) * 256 + x5) = V := by omega
    rw [hv]
  have hp : (x1 :: x2 :: x3 :: x4 :: x5 :: r).length % 5 = r.length % 5 := by
    simp only [List.length_cons]
    omega
  unfold enc32S
  rw [hc, hp]
  simp only [List.append_assoc]
  rfl

theorem octa32_vals (a : List Nat) (t : Nat → Nat) (ht : ∀ v, v < 32 → t (a.getD v 0) = v) (v0 v1 v2 v3 v4 v5 v6 v7 : Nat)
    (h0 : v0 < 32) (h1 : v1 < 32) (h2 : v2 < 32) (h3 : v3 < 32) (h4 : v4 < 32) (h5 : v5 < 32) (h6 : v6 < 32)
    (h7 : v7 < 32) :
    octa32 t ([v0, v1, v2, v3, v4, v5, v6, v7].map (a.getD · 0)) =
      some [(v0 * 8 + v1 / 4) % 256, (v1 * 64 + v2 * 2 + v3 / 16) % 256, (v3 * 16 + v4 / 2) % 256,
            (v4 * 128 + v5 * 4 + v6 / 8) % 256, (v6 * 32 + v7) % 256] := by
  have hm : ([v0, v1, v2, v3, v4, v5, v6, v7].map (a.getD · 0)).map t = [v0, v1, v2, v3, v4, v5, v6, v7] := by
    simp only [List.map_cons, List.map_nil, ht _ h0, ht _ h1, ht _ h2, ht _ h3, ht _ h4, ht _ h5, ht _ h6, ht _ h7]
  have hany : [v0, v1, v2, v3, v4, v5, v6, v7].any (· ≥ 32) = false := by
    simp
    omega
  simp only [octa32, hm, hany, Bool.false_eq_true, if_false]
  rfl

theorem fast32_step (t : Nat → Nat) (C rest o : List Nat) (k : Nat) (out : List Nat) (hl : C.length = 8)
    (h : octa32 t C = some o) : fast32 t (k + 1) (C ++ rest) out = fast32 t k rest (out ++ o) := by
  have h1 : (C ++ rest).length ≥ 8 := by simp only [List.length_append]; omega
  have h2 : (C ++ rest).take 8 = C := by
    rw [List.take_left' hl]
  have h3 : (C ++ rest).drop 8 = rest := by
    rw [List.drop_left' hl]
  rw [fast32, if_pos h1, h2, h, h3]

theorem fast32_group (a : List Nat) (t : Nat → Nat) (ht : ∀ v, v < 32 → t (a.getD v 0) = v)
    (x1 x2 x3 x4 x5 V k : Nat) (out rest : List Nat) (b1 : x1 < 256) (b2 : x2 < 256) (b3 : x3 < 256) (b4 : x4 < 256)
    (b5 : x5 < 256) (hV : V = x1 * 2 ^ 32 + x2 * 2 ^ 24 + x3 * 65536 + x4 * 256 + x5) :
    fast32 t (k + 1) ([V / 2 ^ 35 % 32, V / 2 ^ 30 % 32, V / 2 ^ 25 % 32, V / 2 ^ 20 % 32, V / 2 ^ 15 % 32,
        V / 2 ^ 10 % 32, V / 2 ^ 5 % 32, V / 2 ^ 0 % 32].map (a.getD · 0) ++ rest) out =
      fast32 t k rest (out ++ [x1, x2, x3, x4, x5]) := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := t5 x1 x2 x3 x4 x5 V b1 b2 b3 b4 b5 hV
  rw [e0, e1, e2, e3, e4, e5, e6, e7]
  clear hV e0 e1 e2 e3 e4 e5 e6 e7
  have hO := octa32_vals a t ht (x1 / 8) (x1 % 8 * 4 + x2 / 64) (x2 / 2 % 32) (x2 % 2 * 16 + x3 / 16)
    (x3 % 16 * 2 + x4 / 128) (x4 / 4 % 32) (x4 % 4 * 8 + x5 / 32) (x5 % 32) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [bytes5 x1 x2 x3 x4 x5 b1 b2 b3 b4 b5] at hO
  exact fast32_step t _ _ _ k out (by simp) hO

theorem dec32_main (a : List Nat) (t : Nat → Nat) (ht : ∀ v, v < 32 → t (a.getD v 0) = v)
    (hn : ∀ v, v < 32 → a.getD v 0 ≠ 61) (h61 : 32 ≤ t 61) :
    ∀ (n : Nat) (d : List Nat), d.length ≤ n → (∀ x ∈ d, x < 256) → ∀ (fe ff fr : Nat) (out : List Nat),
      d.length ≤ fe → (enc32S a fe d).length ≤ ff → (enc32S a fe d).length < fr →
      ∃ st, a2b32Run t true none fr (fast32 t ff (enc32S a fe d) out).1
          { out := (fast32 t ff (enc32S a fe d) out).2 } = .ok st ∧ Done32 st (out ++ d) := by
  intro n
  induction n with
  | zero =>
    intro d h _ fe ff fr out _ _ hfr
    have : d = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [enc32S_nil] at hfr ⊢
    obtain ⟨g, rfl⟩ : ∃ g, fr = g + 1 := ⟨fr - 1, by omega⟩
    have hf : fast32 t ff [] out = ([], out) := by cases ff <;> simp [fast32]
    simp [hf, a2b32Run, Done32]
  | succ n ih =>
    intro d h hb fe ff fr out hfe hff hfr
    match d, h, hb, hfe, hff, hfr with
    | [], _, _, _, hff, hfr =>
      rw [enc32S_nil] at hfr ⊢
      obtain ⟨g, rfl⟩ : ∃ g, fr = g + 1 := ⟨fr - 1, by omega⟩
      have hf : fast32 t ff [] out = ([], out) := by cases ff <;> simp [fast32]
      simp [hf, a2b32Run, Done32]
    | [x], _, hb, _, hff, hfr =>
      have hx := hb x (by simp)
      obtain ⟨e0, e1⟩ := t1 x
      rw [enc32S_1, e0, e1] at hff hfr ⊢
      clear e0 e1
      simp only [List.length_append, List.length_map, List.length_cons, List.length_nil, List.length_replicate] at hff hfr
      refine ⟨_, tail32_run a t ht hn h61 _ 6 ff fr out ?_ (by rfl) (by decide) (by simp) (by omega) (by omega), ?_⟩
      · intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        omega
      · simp only [Done32, List.foldl_cons, List.foldl_nil, decStep32]
        refine ⟨?_, by decide, by decide, by decide, Or.inr (by decide)⟩
        simp only [List.append_cancel_left_eq, List.cons.injEq, and_true]
        omega
    | [x, y], _, hb, _, hff, hfr =>
      have hx := hb x (by simp)
      have hy := hb y (by simp)
      obtain ⟨e0, e1, e2, e3⟩ := t2 x y hx hy
      rw [enc32S_2, e0, e1, e2, e3] at hff hfr ⊢
      clear e0 e1 e2 e3
      simp only [List.length_append, List.length_map, List.length_cons, List.length_nil, List.length_replicate] at hff hfr
      refine ⟨_, tail32_run a t ht hn h61 _ 4 ff fr out ?_ (by rfl) (by decide) (by simp) (by omega) (by omega), ?_⟩
      · intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        omega
      · simp only [Done32, List.foldl_cons, List.foldl_nil, decStep32]
        refine ⟨?_, by decide, by decide, by decide, Or.inr (by decide)⟩
        simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_cancel_left_eq, List.cons.injEq,
          and_true]
        constructor <;> omega
    | [x, y, z], _, hb, _, hff, hfr =>
      have hx := hb x (by simp)
      have hy := hb y (by simp)
      have hz := hb z (by simp)
      obtain ⟨e0, e1, e2, e3, e4⟩ := t3 x y z hx hy hz
      rw [enc32S_3, e0, e1, e2, e3, e4] at hff hfr ⊢
      clear e0 e1 e2 e3 e4
      simp only [List.length_append, List.length_map, List.length_cons, List.length_nil, List.length_replicate] at hff hfr
      refine ⟨_, tail32_run a t ht hn h61 _ 3 ff fr out ?_ (by rfl) (by decide) (by simp) (by omega) (by omega), ?_⟩
      · intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        omega
      · simp only [Done32, List.foldl_cons, List.foldl_nil, decStep32]
        refine ⟨?_, by decide, by decide, by decide, Or.inr (by decide)⟩
        simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_cancel_left_eq, List.cons.injEq,
          and_true]
        refine ⟨by omega, by omega, by omega⟩
    | [x, y, z, w], _, hb, _, hff, hfr =>
      have hx := hb x (by simp)
      have hy := hb y (by simp)
      have hz := hb z (by simp)
      have hw := hb w (by simp)
      obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := t4 x y z w hx hy hz hw
      rw [enc32S_4, e0, e1, e2, e3, e4, e5, e6] at hff hfr ⊢
      clear e0 e1 e2 e3 e4 e5 e6
      simp only [List.length_append, List.length_map, List.length_cons, List.length_nil, List.length_replicate] at hff hfr
      refine ⟨_, tail32_run a t ht hn h61 _ 1 ff fr out ?_ (by rfl) (by decide) (by simp) (by omega) (by omega), ?_⟩
      · intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        omega
      · simp only [Done32, List.foldl_cons, List.foldl_nil, decStep32]
        refine ⟨?_, by decide, by decide, by decide, Or.inr (by decide)⟩
        simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_cancel_left_eq, List.cons.injEq,
          and_true]
        refine ⟨by omega, by omega, by omega, by omega⟩
    | x1 :: x2 :: x3 :: x4 :: x5 :: r, h, hb, hfe, hff, hfr =>
      have b1 := hb x1 (by simp)
      have b2 := hb x2 (by simp)
      have b3 := hb x3 (by simp)
      have b4 := hb x4 (by simp)
      have b5 := hb x5 (by simp)
      obtain ⟨fe, rfl⟩ : ∃ k, fe = k + 1 := ⟨fe - 1, by simp only [List.length_cons] at hfe; omega⟩
      generalize hV : x1 * 2 ^ 32 + x2 * 2 ^ 24 + x3 * 65536 + x4 * 256 + x5 = V
      rw [enc32S_5 a fe x1 x2 x3 x4 x5 r V hV.symm] at hff hfr ⊢
      simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at hff hfr
      obtain ⟨k, rfl⟩ : ∃ k, ff = k + 1 := ⟨ff - 1, by omega⟩
      rw [fast32_group a t ht x1 x2 x3 x4 x5 V k out _ b1 b2 b3 b4 b5 hV.symm]
      clear hV
      obtain ⟨st, h1, h2⟩ := ih r (by simp only [List.length_cons] at h; omega) (fun y hy => hb y (by simp [hy])) fe k fr
        (out ++ [x1, x2, x3, x4, x5]) (by simp only [List.length_cons] at hfe; omega) (by omega) (by omega)
      refine ⟨st, h1, ?_⟩
      simpa [List.append_assoc] using h2

/-- `a2b_base32(b2a_base32(d, alphabet=a), alphabet=a) == d`, for an alphabet of 32 distinct bytes without
the padding character, through all four padding lengths. -/
theorem b32_core (a : List Nat) (hl : a.length = 32) (hn : a.Nodup) (h61 : 61 ∉ a) (p : Option Nat)
    (hP : p = none ∨ p = some 61) (d : List Nat) (hd : ∀ x ∈ d, x < 256) :
    a2b32Core (revT a p) true none false (b2a32Core a d true 0) = .ok d := by
  have hm : ∀ v, v < 32 → a.getD v 0 ≠ 61 := by
    intro v hv e
    have hlt : v < a.length := by omega
    have : a.getD v 0 ∈ a := by
      have e : a.getD v 0 = a[v] := by simp [hlt]
      rw [e]
      exact List.getElem_mem hlt
    exact h61 (e ▸ this)
  have ht : ∀ v, v < 32 → revT a p (a.getD v 0) = v := by
    intro v hv
    refine revT_index a _ v hn (by omega) ?_
    intro e
    rcases hP with rfl | rfl
    · cases e
    · exact hm v hv (Option.some.inj e).symm
  have hp : 32 ≤ revT a p 61 := by
    rcases hP with rfl | rfl
    · rw [revT_large a none 61 (by simp) (fun x hx e => h61 (e ▸ hx))]
      omega
    · rw [revT_pad, hl]
      omega
  have e : b2a32Core a d true 0 = enc32S a d.length d := by
    simp [b2a32Core, enc32S]
  rw [e]
  obtain ⟨st, h1, h2, h3, h4, h5, h6⟩ := dec32_main a _ ht hm hp d.length d (Nat.le_refl _) hd d.length
    (enc32S a d.length d).length ((enc32S a d.length d).length + 1) [] (Nat.le_refl _) (Nat.le_refl _) (by omega)
  simp only [a2b32Core, bind, Except.bind, h1]
  have c1 : (st.octa == 1 || st.octa == 3 || st.octa == 6) = false := by
    simp [h3, h4, h5]
  have c2 : ¬ (true = true ∧ st.octa ≠ 0 ∧ st.octa + st.pads < 8) := by
    rcases h6 with h | h <;> simp [h]
  simp only [c1, Bool.false_eq_true, if_false, c2]
  simp [h2, pure, Except.pure]
  omega

/-- `a2b_base32(b2a_base32(d, alphabet=a), alphabet=a) == d` for every alphabet of 32 distinct bytes that
leaves out `=`, which is where `get_reverse_table` matters: it has to invert the alphabet. -/
def B32AlphabetRoundTrip : Prop :=
  ∀ a d out : List Nat, a.length = 32 → a.Nodup → 61 ∉ a → (∀ x ∈ d, x < 256) →
    b2aB32 (.bytes d) true 0 (some (.bytes a)) = .ok out →
    a2bB32 (.bytes out) true (.bytes a) (.bytes []) false = .ok d

theorem b32AlphabetRoundTrip_proven : B32AlphabetRoundTrip := by
  intro a d out hl hn h61 hd h
  have h1 : out = b2a32Core a d true 0 := by
    simp [b2aB32, bufData, sizeT, bufOpt, encTable, hl, bind, Except.bind, pure, Except.pure] at h
    exact h.symm
  subst h1
  simpa [a2bB32, asciiBuffer, alphaDec, bufData, decTable, hl, bind, Except.bind, pure, Except.pure] using
    b32_core a hl hn h61 _ (Or.inr rfl) d hd

/-- `b32decode(b32encode(d)) == d` and `b32hexdecode(b32hexencode(d)) == d`, for every `bytes` value. -/
def B32RoundTripC : Prop :=
  ∀ d out : List Nat, (∀ x ∈ d, x < 256) →
    (b2aB32 (.bytes d) true 0 none = .ok out → pyB32decode (.bytes out) false none true (.bytes []) false = .ok d) ∧
    (b2aB32 (.bytes d) true 0 (some (.bytes b32hexAlpha)) = .ok out →
      pyB32hexdecode (.bytes out) false true (.bytes []) false = .ok d)

theorem b32Alpha_len : b32Alpha.length = 32 := by decide
theorem b32hexAlpha_len : b32hexAlpha.length = 32 := by decide
theorem b32Alpha_nodup : b32Alpha.Nodup := by decide +kernel
theorem b32hexAlpha_nodup : b32hexAlpha.Nodup := by decide +kernel
theorem b32Alpha_pad : 61 ∉ b32Alpha := by decide +kernel
theorem b32hexAlpha_pad : 61 ∉ b32hexAlpha := by decide +kernel

theorem b32RoundTripC_proven : B32RoundTripC := by
  intro d out hd
  constructor
  · intro h
    have h1 : out = b2a32Core b32Alpha d true 0 := by
      simp [b2aB32, bufData, sizeT, bufOpt, encTable, bind, Except.bind, pure, Except.pure] at h
      exact h.symm
    subst h1
    simpa [pyB32decode, bytesFromDecodeData, a2bB32, asciiBuffer, alphaDec, bufData, decTable, bind, Except.bind, pure,
      Except.pure] using b32_core b32Alpha b32Alpha_len b32Alpha_nodup b32Alpha_pad _ (Or.inl rfl) d hd
  · intro h
    have h1 : out = b2a32Core b32hexAlpha d true 0 := by
      simp [b2aB32, bufData, sizeT, bufOpt, encTable, b32hexAlpha_len, bind, Except.bind, pure, Except.pure] at h
      exact h.symm
    subst h1
    simpa [pyB32hexdecode, bytesFromDecodeData, a2bB32, asciiBuffer, alphaDec, bufData, decTable, b32hexAlpha_len, bind,
      Except.bind, pure, Except.pure] using b32_core b32hexAlpha b32hexAlpha_len b32hexAlpha_nodup b32hexAlpha_pad _ (Or.inr rfl) d hd

/-! ### base85 -/

theorem digits85_eq (t : List Nat) (w : Nat) :
    digits85 t w = [t.getD (w / 52200625 % 85) 0, t.getD (w / 614125 % 85) 0, t.getD (w / 7225 % 85) 0,
      t.getD (w / 85 % 85) 0, t.getD (w / 1 % 85) 0] := rfl

theorem word4_4 (w : Nat) :
    word4 w 4 = [w / 16777216 % 256, w / 65536 % 256, w / 256 % 256, w / 1 % 256] := rfl
theorem word4_3 (w : Nat) : word4 w 3 = [w / 16777216 % 256, w / 65536 % 256, w / 256 % 256] := rfl
theorem word4_2 (w : Nat) : word4 w 2 = [w / 16777216 % 256, w / 65536 % 256] := rfl
theorem word4_1 (w : Nat) : word4 w 1 = [w / 16777216 % 256] := rfl

theorem wordOf_1 (x : Nat) : wordOf [x] = x * 16777216 := by
  simp [wordOf]
  omega
theorem wordOf_2 (x y : Nat) : wordOf [x, y] = x * 16777216 + y * 65536 := by
  simp [wordOf]
  omega
theorem wordOf_3 (x y z : Nat) : wordOf [x, y, z] = x * 16777216 + y * 65536 + z * 256 := by
  simp [wordOf]
  omega
theorem wordOf_4 (x y z e : Nat) : wordOf [x, y, z, e] = x * 16777216 + y * 65536 + z * 256 + e := by
  simp [wordOf]
  omega

/-- A digit, not the fifth. -/
theorem b85_d (t : Nat → Nat) (N f c v l p : Nat) (o r : List Nat) (len : Int) (hv : t c = v) (h85 : v < 85)
    (hlen : 0 < len) (hp : p < 4) :
    a2bB85Loop t none false N (f + 1) (c :: r) len ⟨l, p, o⟩ =
      a2bB85Loop t none false N f r (len - 1) ⟨l * 85 + v, p + 1, o⟩ := by
  have h1 : decide (len ≤ 0) = false := by simp; omega
  have h2 : (p == 4) = false := by simp; omega
  have h3 : (p + 1 != 5) = true := by simp; omega
  simp only [a2bB85Loop, h1, Bool.false_and, Bool.false_eq_true, if_false, hv, h85, if_true, h2, h3]

/-- The fifth digit of a whole group. -/
theorem b85_d5 (t : Nat → Nat) (N f c v l : Nat) (o r : List Nat) (len : Int) (hv : t c = v) (h85 : v < 85)
    (hlen : 0 < len) (hov : l * 85 + v < 2 ^ 32) :
    a2bB85Loop t none false N (f + 1) (c :: r) len ⟨l, 4, o⟩ =
      a2bB85Loop t none false N f r (len - 1) ⟨0, 0, o ++ word4 (l * 85 + v) 4⟩ := by
  have h1 : decide (len ≤ 0) = false := by simp; omega
  have h2 : decide (l * 85 + v ≥ 2 ^ 32) = false := by simp; omega
  have h3 : ¬ len < 1 := by omega
  simp only [a2bB85Loop, h1, Bool.false_and, Bool.false_eq_true, if_false, hv, h85, if_true, h2, beq_self_eq_true,
    Bool.true_and, h3]
  rfl

/-- A padding digit, not the fifth. -/
theorem b85_n (t : Nat → Nat) (N f l p : Nat) (o : List Nat) (len : Int) (hp0 : p ≠ 0) (hp : p < 4) :
    a2bB85Loop t none false N (f + 1) [] len ⟨l, p, o⟩ =
      a2bB85Loop t none false N f [] (len - 1) ⟨l * 85 + 84, p + 1, o⟩ := by
  have h1 : (p == 0) = false := by simpa using hp0
  have h2 : (p == 4) = false := by simp; omega
  have h3 : (p + 1 != 5) = true := by simp; omega
  simp only [a2bB85Loop, h1, Bool.and_false, Bool.false_eq_true, if_false, h2, h3]
  simp

/-- The fifth digit of a cut group. -/
theorem b85_n5 (t : Nat → Nat) (N f l k : Nat) (o : List Nat) (len : Int) (hlen : len = (k : Int) - 3) (hk0 : k ≠ 0)
    (hk : k < 4) (hov : l * 85 + 84 < 2 ^ 32) :
    a2bB85Loop t none false N (f + 1) [] len ⟨l, 4, o⟩ =
      a2bB85Loop t none false N f [] (len - 1) ⟨0, 0, o ++ word4 (l * 85 + 84) k⟩ := by
  have h1 : (4 == 0) = false := by decide
  have h2 : decide (l * 85 + 84 ≥ 2 ^ 32) = false := by simp; omega
  have h3 : len < 1 := by omega
  have h4 : (3 + len).toNat = k := by omega
  have h5 : ¬ k = 0 := hk0
  have h6 : ¬ 4294967212 ≤ l * 85 := by omega
  simp only [a2bB85Loop, Bool.and_false, Bool.false_eq_true, if_false, beq_self_eq_true, Bool.true_and, h3, if_true, h4,
    h5]
  simp [h6]

theorem b85_end (t : Nat → Nat) (N f : Nat) (o : List Nat) (len : Int) (hlen : len ≤ 0) :
    a2bB85Loop t none false N (f + 1) [] len ⟨0, 0, o⟩ = .ok ⟨0, 0, o⟩ := by
  have h1 : decide (len ≤ 0) = true := by simp; omega
  simp [a2bB85Loop, h1]

/-- A whole group. -/
theorem b85_group (a : List Nat) (t : Nat → Nat) (ht : ∀ v, v < 85 → t (a.getD v 0) = v) (N f w : Nat) (o r : List Nat)
    (len : Int) (hw : w < 2 ^ 32) (hlen : len = (r.length : Int) + 5) :
    a2bB85Loop t none false N (f + 5) (digits85 a w ++ r) len ⟨0, 0, o⟩ =
      a2bB85Loop t none false N f r r.length ⟨0, 0, o ++ word4 w 4⟩ := by
  rw [digits85_eq]
  simp only [List.cons_append, List.nil_append]
  rw [b85_d t N (f + 4) _ _ 0 0 o _ len (ht _ (Nat.mod_lt _ (by decide))) (Nat.mod_lt _ (by decide)) (by omega) (by omega),
    b85_d t N (f + 3) _ _ _ _ o _ _ (ht _ (Nat.mod_lt _ (by decide))) (Nat.mod_lt _ (by decide)) (by omega) (by omega),
    b85_d t N (f + 2) _ _ _ _ o _ _ (ht _ (Nat.mod_lt _ (by decide))) (Nat.mod_lt _ (by decide)) (by omega) (by omega),
    b85_d t N (f + 1) _ _ _ _ o _ _ (ht _ (Nat.mod_lt _ (by decide))) (Nat.mod_lt _ (by decide)) (by omega) (by omega)]
  have hw2 : (((0 * 85 + w / 52200625 % 85) * 85 + w / 614125 % 85) * 85 + w / 7225 % 85) * 85 + w / 85 % 85 = w / 85 := by
    omega
  have e : 0 + 1 + 1 + 1 + 1 = 4 := rfl
  rw [hw2, e, b85_d5 t N f _ _ _ o _ _ (ht _ (Nat.mod_lt _ (by decide))) (Nat.mod_lt _ (by decide)) (by omega) (by omega)]
  have hw3 : w / 85 * 85 + w / 1 % 85 = w := by omega
  have e2 : len - 1 - 1 - 1 - 1 - 1 = (r.length : Int) := by omega
  rw [hw3, e2]

/-- What `binascii_b2a_base85_impl` writes with `pad=False`, with `fe` as the fuel of its loop. -/
def enc85S (a : List Nat) (fe : Nat) (d : List Nat) : List Nat :=
  (fullB85 a fe d).1 ++
    (if (fullB85 a fe d).2.isEmpty then [] else
      (digits85 a (wordOf (fullB85 a fe d).2)).take ((fullB85 a fe d).2.length + 1))

theorem full85_short (a d : List Nat) (f : Nat) (h : d.length < 4) : fullB85 a f d = ([], d) := by
  cases f with
  | zero => rfl
  | succ f =>
    simp only [fullB85]
    rw [if_neg (by omega)]

theorem enc85S_nil (a : List Nat) (fe : Nat) : enc85S a fe [] = [] := by
  unfold enc85S
  rw [full85_short a [] fe (by simp)]
  rfl

theorem enc85S_short (a d : List Nat) (fe : Nat) (h : d.length < 4) (hd : d ≠ []) :
    enc85S a fe d = (digits85 a (wordOf d)).take (d.length + 1) := by
  unfold enc85S
  rw [full85_short a d fe h]
  cases d with
  | nil => exact absurd rfl hd
  | cons x r => rfl

theorem enc85S_4 (a : List Nat) (fe x y z e : Nat) (r : List Nat) :
    enc85S a (fe + 1) (x :: y :: z :: e :: r) = digits85 a (wordOf [x, y, z, e]) ++ enc85S a fe r := by
  have ht : (x :: y :: z :: e :: r).take 4 = [x, y, z, e] := rfl
  have hd : (x :: y :: z :: e :: r).drop 4 = r := rfl
  have hc : fullB85 a (fe + 1) (x :: y :: z :: e :: r) =
      (digits85 a (wordOf [x, y, z, e]) ++ (fullB85 a fe r).1, (fullB85 a fe r).2) := by
    rw [fullB85, if_pos (by simp only [List.length_cons]; omega)]
    simp only [ht, hd]
  unfold enc85S
  rw [hc]
  simp only [List.append_assoc]

/-- The padding digits `~` raise a cut group by less than its lowest kept digit: the word stays a word and
keeps the bytes it was made from. -/
theorem pad3 (w : Nat) : ((w / 614125 * 85 + 84) * 85 + 84) * 85 + 84 = w + (614124 - w % 614125) := by omega
theorem pad2 (w : Nat) : (w / 7225 * 85 + 84) * 85 + 84 = w + (7224 - w % 7225) := by omega
theorem pad1 (w : Nat) : w / 85 * 85 + 84 = w + (84 - w % 85) := by omega

theorem d2 (w : Nat) (h : w < 2 ^ 32) : (0 * 85 + w / 52200625 % 85) * 85 + w / 614125 % 85 = w / 614125 := by omega
theorem d3 (w : Nat) (h : w < 2 ^ 32) :
    ((0 * 85 + w / 52200625 % 85) * 85 + w / 614125 % 85) * 85 + w / 7225 % 85 = w / 7225 := by omega
theorem d4 (w : Nat) (h : w < 2 ^ 32) :
    (((0 * 85 + w / 52200625 % 85) * 85 + w / 614125 % 85) * 85 + w / 7225 % 85) * 85 + w / 85 % 85 = w / 85 := by omega

theorem cut1 (x δ : Nat) (hx : x < 256) (h : δ < 16777216) : word4 (x * 16777216 + δ) 1 = [x] := by
  rw [word4_1]
  simp only [List.cons.injEq, and_true]
  omega

theorem cut2 (x y δ : Nat) (hx : x < 256) (hy : y < 256) (h : δ < 65536) :
    word4 (x * 16777216 + y * 65536 + δ) 2 = [x, y] := by
  rw [word4_2]
  simp only [List.cons.injEq, and_true]
  constructor <;> omega

theorem cut3 (x y z δ : Nat) (hx : x < 256) (hy : y < 256) (hz : z < 256) (h : δ < 256) :
    word4 (x * 16777216 + y * 65536 + z * 256 + δ) 3 = [x, y, z] := by
  rw [word4_3]
  simp only [List.cons.injEq, and_true]
  refine ⟨by omega, by omega, by omega⟩

theorem dec85_main (a : List Nat) (t : Nat → Nat) (ht : ∀ v, v < 85 → t (a.getD v 0) = v) (N : Nat) :
    ∀ (n : Nat) (d : List Nat), d.length ≤ n → (∀ x ∈ d, x < 256) → ∀ (fe f : Nat) (o : List Nat),
      d.length ≤ fe → (enc85S a fe d).length + 6 ≤ f →
      a2bB85Loop t none false N f (enc85S a fe d) (enc85S a fe d).length ⟨0, 0, o⟩ = .ok ⟨0, 0, o ++ d⟩ := by
  intro n
  induction n with
  | zero =>
    intro d h _ fe f o _ hf
    have : d = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [enc85S_nil] at hf ⊢
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simpa using b85_end t N g o 0 (by omega)
  | succ n ih =>
    intro d h hb fe f o hfe hf
    match d, h, hb, hfe, hf with
    | [], _, _, _, hf =>
      rw [enc85S_nil] at hf ⊢
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      simpa using b85_end t N g o 0 (by omega)
    | [x], _, hb, _, hf =>
      have hx := hb x (by simp)
      rw [enc85S_short a [x] fe (by simp) (by simp), wordOf_1, digits85_eq] at hf ⊢
      simp only [List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero, Nat.zero_add] at hf ⊢
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 6 := ⟨f - 6, by omega⟩
      generalize hw : x * 16777216 = w at *
      have hb1 : w ≤ 4278190080 := by omega
      have c0 := Nat.mod_lt (w / 52200625) (show 85 > 0 by decide)
      have c1 := Nat.mod_lt (w / 614125) (show 85 > 0 by decide)
      have e1 := d2 w (by omega)
      have e2 : 0 + 1 + 1 + 1 + 1 = 4 := rfl
      rw [b85_d t N (g + 5) _ _ 0 0 o _ _ (ht _ c0) c0 (by omega) (by omega),
        b85_d t N (g + 4) _ _ _ _ o _ _ (ht _ c1) c1 (by omega) (by omega), e1,
        b85_n t N (g + 3) _ _ o _ (by omega) (by omega), b85_n t N (g + 2) _ _ o _ (by omega) (by omega), e2,
        b85_n5 t N (g + 1) _ 1 o _ (by omega) (by decide) (by decide) (by rw [pad3]; omega),
        b85_end t N g _ _ (by omega), pad3, ← hw, cut1 x _ hx (by omega)]
    | [x, y], _, hb, _, hf =>
      have hx := hb x (by simp)
      have hy := hb y (by simp)
      rw [enc85S_short a [x, y] fe (by simp) (by simp), wordOf_2, digits85_eq] at hf ⊢
      simp only [List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero, Nat.zero_add] at hf ⊢
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 6 := ⟨f - 6, by omega⟩
      generalize hw : x * 16777216 + y * 65536 = w at *
      have hb1 : w ≤ 4294901760 := by omega
      have c0 := Nat.mod_lt (w / 52200625) (show 85 > 0 by decide)
      have c1 := Nat.mod_lt (w / 614125) (show 85 > 0 by decide)
      have c2 := Nat.mod_lt (w / 7225) (show 85 > 0 by decide)
      have e1 := d3 w (by omega)
      have e2 : 0 + 1 + 1 + 1 + 1 = 4 := rfl
      rw [b85_d t N (g + 5) _ _ 0 0 o _ _ (ht _ c0) c0 (by omega) (by omega),
        b85_d t N (g + 4) _ _ _ _ o _ _ (ht _ c1) c1 (by omega) (by omega),
        b85_d t N (g + 3) _ _ _ _ o _ _ (ht _ c2) c2 (by omega) (by omega), e1,
        b85_n t N (g + 2) _ _ o _ (by omega) (by omega), e2,
        b85_n5 t N (g + 1) _ 2 o _ (by omega) (by decide) (by decide) (by rw [pad2]; omega),
        b85_end t N g _ _ (by omega), pad2, ← hw, cut2 x y _ hx hy (by omega)]
    | [x, y, z], _, hb, _, hf =>
      have hx := hb x (by simp)
      have hy := hb y (by simp)
      have hz := hb z (by simp)
      rw [enc85S_short a [x, y, z] fe (by simp) (by simp), wordOf_3, digits85_eq] at hf ⊢
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
      rw [b85_d t N (g + 5) _ _ 0 0 o _ _ (ht _ c0) c0 (by omega) (by omega),
        b85_d t N (g + 4) _ _ _ _ o _ _ (ht _ c1) c1 (by omega) (by omega),
        b85_d t N (g + 3) _ _ _ _ o _ _ (ht _ c2) c2 (by omega) (by omega),
        b85_d t N (g + 2) _ _ _ _ o _ _ (ht _ c3) c3 (by omega) (by omega), e1, e2,
        b85_n5 t N (g + 1) _ 3 o _ (by omega) (by decide) (by decide) (by rw [pad1]; omega),
        b85_end t N g _ _ (by omega), pad1, ← hw, cut3 x y z _ hx hy hz (by omega)]
    | x :: y :: z :: e :: r, h, hb, hfe, hf =>
      have hx := hb x (by simp)
      have hy := hb y (by simp)
      have hz := hb z (by simp)
      have he := hb e (by simp)
      obtain ⟨fe, rfl⟩ : ∃ k, fe = k + 1 := ⟨fe - 1, by simp only [List.length_cons] at hfe; omega⟩
      rw [enc85S_4] at hf ⊢
      have hlenD : (digits85 a (wordOf [x, y, z, e])).length = 5 := rfl
      rw [List.length_append, hlenD] at hf ⊢
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 5 := ⟨f - 5, by omega⟩
      rw [b85_group a t ht N g _ o _ _ (by rw [wordOf_4]; omega) (by push_cast; omega)]
      have hr := ih r (by simp only [List.length_cons] at h; omega) (fun y hy => hb y (by simp [hy])) fe g
        (o ++ word4 (wordOf [x, y, z, e]) 4) (by simp only [List.length_cons] at hfe; omega) (by omega)
      have hbytes : word4 (wordOf [x, y, z, e]) 4 = [x, y, z, e] := by
        rw [word4_4, wordOf_4]
        simp only [List.cons.injEq, and_true]
        refine ⟨by omega, by omega, by omega, by omega⟩
      rw [hbytes] at hr ⊢
      rw [hr]
      simp [List.append_assoc]

/-- `a2b_base85(b2a_base85(d, alphabet=a), alphabet=a) == d`, for an alphabet of 85 distinct bytes. -/
theorem b85_core (a : List Nat) (hl : a.length = 85) (hn : a.Nodup) (d : List Nat) (hd : ∀ x ∈ d, x < 256) (N : Nat) :
    a2bB85Loop (revT a none) none false N ((b2aB85Core a d false 0).length + 6) (b2aB85Core a d false 0)
      (b2aB85Core a d false 0).length {} = .ok ⟨0, 0, d⟩ := by
  have ht : ∀ v, v < 85 → revT a none (a.getD v 0) = v := by
    intro v hv
    exact revT_index a none v hn (by omega) (by simp)
  have e : b2aB85Core a d false 0 = enc85S a d.length d := by
    simp [b2aB85Core, enc85S]
  rw [e]
  simpa using dec85_main a _ ht N d.length d (Nat.le_refl _) hd d.length _ [] (Nat.le_refl _) (Nat.le_refl _)

/-- `a2b_base85(b2a_base85(d, alphabet=a), alphabet=a) == d` for every alphabet of 85 distinct bytes. -/
def B85AlphabetRoundTrip : Prop :=
  ∀ a d out : List Nat, a.length = 85 → a.Nodup → (∀ x ∈ d, x < 256) →
    b2aB85 (.bytes d) false 0 (some (.bytes a)) = .ok out →
    a2bB85 (.bytes out) (.bytes a) (.bytes []) false = .ok d

theorem b85AlphabetRoundTrip_proven : B85AlphabetRoundTrip := by
  intro a d out hl hn hd h
  have h1 : out = b2aB85Core a d false 0 := by
    simp [b2aB85, bufData, sizeT, bufOpt, encTable, hl, bind, Except.bind, pure, Except.pure] at h
    exact h.symm
  subst h1
  have := b85_core a hl hn d hd (b2aB85Core a d false 0).length
  simp [a2bB85, asciiBuffer, alphaDec, bufData, decTable, hl, bind, Except.bind, pure, Except.pure, this]

/-- `b85decode(b85encode(d)) == d`, including a cut last group. -/
def B85RoundTripC : Prop :=
  ∀ d out : List Nat, (∀ x ∈ d, x < 256) → b2aB85 (.bytes d) false 0 none = .ok out →
    a2bB85 (.bytes out) .absent (.bytes []) false = .ok d

theorem b85Alpha_len : b85Alpha.length = 85 := by decide
theorem b85Alpha_nodup : b85Alpha.Nodup := by decide +kernel
theorem z85Alpha_len : z85Alpha.length = 85 := by decide
theorem z85Alpha_nodup : z85Alpha.Nodup := by decide +kernel

theorem b85RoundTripC_proven : B85RoundTripC := by
  intro d out hd h
  have h1 : out = b2aB85Core b85Alpha d false 0 := by
    simp [b2aB85, bufData, sizeT, bufOpt, encTable, bind, Except.bind, pure, Except.pure] at h
    exact h.symm
  subst h1
  have := b85_core b85Alpha b85Alpha_len b85Alpha_nodup d hd (b2aB85Core b85Alpha d false 0).length
  simp [a2bB85, asciiBuffer, alphaDec, bufData, decTable, bind, Except.bind, pure, Except.pure, this]

/-- `z85decode(z85encode(d)) == d`. -/
def Z85RoundTripC : Prop :=
  ∀ d out : List Nat, (∀ x ∈ d, x < 256) → b2aB85 (.bytes d) false 0 (some (.bytes z85Alpha)) = .ok out →
    a2bB85 (.bytes out) (.bytes z85Alpha) (.bytes []) false = .ok d

theorem z85RoundTripC_proven : Z85RoundTripC :=
  fun d out hd h => b85AlphabetRoundTrip_proven z85Alpha d out z85Alpha_len z85Alpha_nodup hd h

/-! ### Ascii85 -/

theorem a85_d (ig : List Nat) (fs : Bool) (f c v l p : Nat) (z : Bool) (o r : List Nat) (len : Int)
    (hv : revT a85Alpha none c = v) (h85 : v < 85) (hlen : 0 < len) (hp : p < 4) :
    a2bA85Loop fs false ig (f + 1) (c :: r) len ⟨l, p, z, o⟩ =
      a2bA85Loop fs false ig f r (len - 1) ⟨l * 85 + v, p + 1, z, o⟩ := by
  have h1 : decide (len ≤ 0) = false := by simp; omega
  have h2 : (p == 4) = false := by simp; omega
  have h3 : (p + 1 != 5) = true := by simp; omega
  simp only [a2bA85Loop, h1, Bool.false_and, Bool.false_eq_true, if_false, hv, h85, if_true, h2, h3]

theorem flush_full (len : Int) (st : Dec85) (hlen : 0 < len) :
    flushA85 false len st = .ok { out := st.out ++ word4 st.left 4 } := by
  have h3 : ¬ len < 1 := by omega
  simp [flushA85, h3]

theorem flush_cut (len : Int) (st : Dec85) (k : Nat) (hlen : len = (k : Int) - 3) (hk0 : k ≠ 0) (hk : k < 4) :
    flushA85 false len st = .ok { out := st.out ++ word4 st.left k } := by
  have h3 : len < 1 := by omega
  have h4 : (3 + len).toNat = k := by omega
  have h5 : ¬ k = 0 := hk0
  simp [flushA85, h3, h4, h5]

theorem a85_d5 (ig : List Nat) (fs : Bool) (f c v l : Nat) (z : Bool) (o r : List Nat) (len : Int)
    (hv : revT a85Alpha none c = v) (h85 : v < 85) (hlen : 0 < len) (hov : l * 85 + v < 2 ^ 32) :
    a2bA85Loop fs false ig (f + 1) (c :: r) len ⟨l, 4, z, o⟩ =
      a2bA85Loop fs false ig f r (len - 1) { out := o ++ word4 (l * 85 + v) 4 } := by
  have h1 : decide (len ≤ 0) = false := by simp; omega
  have h2 : decide (l * 85 + v ≥ 2 ^ 32) = false := by simp; omega
  simp only [a2bA85Loop, h1, Bool.false_and, Bool.false_eq_true, if_false, hv, h85, if_true, h2, beq_self_eq_true,
    Bool.true_and]
  have h3 : (4 + 1 != 5) = false := by decide
  simp only [h3, Bool.false_eq_true, if_false, flush_full len _ hlen]

theorem a85_n (ig : List Nat) (fs : Bool) (f l p : Nat) (z : Bool) (o : List Nat) (len : Int) (hp0 : p ≠ 0) (hp : p < 4) :
    a2bA85Loop fs false ig (f + 1) [] len ⟨l, p, z, o⟩ =
      a2bA85Loop fs false ig f [] (len - 1) ⟨l * 85 + 84, p + 1, z, o⟩ := by
  have h1 : (p == 0) = false := by simpa using hp0
  have h2 : (p == 4) = false := by simp; omega
  have h3 : (p + 1 != 5) = true := by simp; omega
  simp only [a2bA85Loop, h1, Bool.and_false, Bool.false_eq_true, if_false, h2, h3]
  simp

theorem a85_n5 (ig : List Nat) (fs : Bool) (f l k : Nat) (z : Bool) (o : List Nat) (len : Int)
    (hlen : len = (k : Int) - 3) (hk0 : k ≠ 0) (hk : k < 4) (hov : l * 85 + 84 < 2 ^ 32) :
    a2bA85Loop fs false ig (f + 1) [] len ⟨l, 4, z, o⟩ =
      a2bA85Loop fs false ig f [] (len - 1) { out := o ++ word4 (l * 85 + 84) k } := by
  have h2 : decide (l * 85 + 84 ≥ 2 ^ 32) = false := by simp; omega
  simp only [a2bA85Loop, Bool.and_false, Bool.false_eq_true, if_false, beq_self_eq_true, Bool.true_and, h2]
  simp [flush_cut len _ k hlen hk0 hk]

theorem a85_end (ig : List Nat) (fs : Bool) (f : Nat) (o : List Nat) (len : Int) (hlen : len ≤ 0) :
    a2bA85Loop fs false ig (f + 1) [] len { out := o } = .ok { out := o } := by
  have h1 : decide (len ≤ 0) = true := by simp; omega
  simp [a2bA85Loop, h1]

theorem a85_rev : ∀ v, v < 85 → revT a85Alpha none (a85Alpha.getD v 0) = v := by decide +kernel

theorem a85_group (ig : List Nat) (fs : Bool) (f w : Nat) (o r : List Nat) (len : Int) (hw : w < 2 ^ 32)
    (hlen : len = (r.length : Int) + 5) :
    a2bA85Loop fs false ig (f + 5) (digits85 a85Alpha w ++ r) len { out := o } =
      a2bA85Loop fs false ig f r r.length { out := o ++ word4 w 4 } := by
  have hg : ∀ x, revT a85Alpha none (a85Alpha.getD (x % 85) 0) = x % 85 := fun x => a85_rev _ (Nat.mod_lt _ (by decide))
  rw [digits85_eq]
  simp only [List.cons_append, List.nil_append]
  have s0 : ({ out := o } : Dec85) = ⟨0, 0, false, o⟩ := rfl
  rw [s0, a85_d ig fs (f + 4) _ _ 0 0 false o _ len (hg _) (Nat.mod_lt _ (by decide)) (by omega) (by omega),
    a85_d ig fs (f + 3) _ _ _ _ false o _ _ (hg _) (Nat.mod_lt _ (by decide)) (by omega) (by omega),
    a85_d ig fs (f + 2) _ _ _ _ false o _ _ (hg _) (Nat.mod_lt _ (by decide)) (by omega) (by omega),
    a85_d ig fs (f + 1) _ _ _ _ false o _ _ (hg _) (Nat.mod_lt _ (by decide)) (by omega) (by omega)]
  have hw2 : (((0 * 85 + w / 52200625 % 85) * 85 + w / 614125 % 85) * 85 + w / 7225 % 85) * 85 + w / 85 % 85 = w / 85 := by
    omega
  have e : 0 + 1 + 1 + 1 + 1 = 4 := rfl
  rw [hw2, e, a85_d5 ig fs f _ _ _ false o _ _ (hg _) (Nat.mod_lt _ (by decide)) (by omega) (by omega)]
  have hw3 : w / 85 * 85 + w / 1 % 85 = w := by omega
  have e2 : len - 1 - 1 - 1 - 1 - 1 = (r.length : Int) := by omega
  rw [hw3, e2]

/-- `z`, for a group of zeros, and `y`, for four spaces with `foldspaces`. -/
theorem a85_fold (ig : List Nat) (fs : Bool) (f c : Nat) (o r : List Nat) (len : Int) (hlen : 0 < len)
    (hc : c = 122 ∨ (c = 121 ∧ fs = true)) :
    a2bA85Loop fs false ig (f + 1) (c :: r) len { out := o } =
      a2bA85Loop fs false ig f r (len - 1) { out := o ++ word4 (if c == 121 then 0x20202020 else 0) 4 } := by
  have h1 : decide (len ≤ 0) = false := by simp; omega
  have hr : ¬ revT a85Alpha none c < 85 := by
    rcases hc with h | ⟨h, _⟩ <;> subst h <;> decide +kernel
  have hb : ((c == 121 && fs) || c == 122) = true := by
    rcases hc with h | ⟨h, h2⟩ <;> subst h <;> simp [*]
  simp only [a2bA85Loop, h1, Bool.false_and, Bool.false_eq_true, if_false, hr, hb, if_true]
  have h0 : (0 != 0) = false := by decide
  have h5 : (5 != 5) = false := by decide
  simp only [h0, h5, Bool.false_eq_true, if_false, flush_full len _ hlen, Option.getD_some, hb, if_true]

/-- What `binascii_b2a_ascii85_impl` writes with its options off, with `fe` as the fuel of its loop. -/
def enc85A (fs : Bool) (fe : Nat) (d : List Nat) : List Nat :=
  (fullA85 fs fe d).1 ++ partA85 false (fullA85 fs fe d).2

theorem fullA_short (fs : Bool) (d : List Nat) (f : Nat) (h : d.length < 4) : fullA85 fs f d = ([], d) := by
  cases f with
  | zero => rfl
  | succ f =>
    simp only [fullA85]
    rw [if_neg (by omega)]

theorem enc85A_nil (fs : Bool) (fe : Nat) : enc85A fs fe [] = [] := by
  unfold enc85A
  rw [fullA_short fs [] fe (by simp)]
  rfl

theorem enc85A_short (fs : Bool) (d : List Nat) (fe : Nat) (h : d.length < 4) (hd : d ≠ []) :
    enc85A fs fe d = (digits85 a85Alpha (wordOf d)).take (d.length + 1) := by
  unfold enc85A
  rw [fullA_short fs d fe h]
  cases d with
  | nil => exact absurd rfl hd
  | cons x r => simp [partA85]

theorem enc85A_4 (fs : Bool) (fe x y z e : Nat) (r : List Nat) :
    enc85A fs (fe + 1) (x :: y :: z :: e :: r) =
      (if wordOf [x, y, z, e] == 0 then [122]
       else if fs && wordOf [x, y, z, e] == 0x20202020 then [121]
       else digits85 a85Alpha (wordOf [x, y, z, e])) ++ enc85A fs fe r := by
  have ht : (x :: y :: z :: e :: r).take 4 = [x, y, z, e] := rfl
  have hd : (x :: y :: z :: e :: r).drop 4 = r := rfl
  have hc : fullA85 fs (fe + 1) (x :: y :: z :: e :: r) =
      ((if wordOf [x, y, z, e] == 0 then [122]
        else if fs && wordOf [x, y, z, e] == 0x20202020 then [121]
        else digits85 a85Alpha (wordOf [x, y, z, e])) ++ (fullA85 fs fe r).1, (fullA85 fs fe r).2) := by
    rw [fullA85, if_pos (by simp only [List.length_cons]; omega)]
    simp only [ht, hd]
  unfold enc85A
  rw [hc]
  simp only [List.append_assoc]

theorem dec85A_main (ig : List Nat) (fs : Bool) :
    ∀ (n : Nat) (d : List Nat), d.length ≤ n → (∀ x ∈ d, x < 256) → ∀ (fe f : Nat) (o : List Nat),
      d.length ≤ fe → (enc85A fs fe d).length + 6 ≤ f →
      a2bA85Loop fs false ig f (enc85A fs fe d) (enc85A fs fe d).length { out := o } = .ok { out := o ++ d } := by
  have hg : ∀ x, revT a85Alpha none (a85Alpha.getD (x % 85) 0) = x % 85 := fun x => a85_rev _ (Nat.mod_lt _ (by decide))
  intro n
  induction n with
  | zero =>
    intro d h _ fe f o _ hf
    have : d = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [enc85A_nil] at hf ⊢
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simpa using a85_end ig fs g o 0 (by omega)
  | succ n ih =>
    intro d h hb fe f o hfe hf
    have s0 : ({ out := o } : Dec85) = ⟨0, 0, false, o⟩ := rfl
    match d, h, hb, hfe, hf with
    | [], _, _, _, hf =>
      rw [enc85A_nil] at hf ⊢
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      simpa using a85_end ig fs g o 0 (by omega)
    | [x], _, hb, _, hf =>
      have hx := hb x (by simp)
      rw [enc85A_short fs [x] fe (by simp) (by simp), wordOf_1, digits85_eq] at hf ⊢
      simp only [List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero, Nat.zero_add] at hf ⊢
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 6 := ⟨f - 6, by omega⟩
      generalize hw : x * 16777216 = w at *
      have hb1 : w ≤ 4278190080 := by omega
      have e1 := d2 w (by omega)
      have e2 : 0 + 1 + 1 + 1 + 1 = 4 := rfl
      rw [s0, a85_d ig fs (g + 5) _ _ 0 0 false o _ _ (hg _) (Nat.mod_lt _ (by decide)) (by omega) (by omega),
        a85_d ig fs (g + 4) _ _ _ _ false o _ _ (hg _) (Nat.mod_lt _ (by decide)) (by omega) (by omega), e1,
        a85_n ig fs (g + 3) _ _ false o _ (by omega) (by omega), a85_n ig fs (g + 2) _ _ false o _ (by omega) (by omega), e2,
        a85_n5 ig fs (g + 1) _ 1 false o _ (by omega) (by decide) (by decide) (by rw [pad3]; omega),
        a85_end ig fs g _ _ (by omega), pad3, ← hw, cut1 x _ hx (by omega)]
    | [x, y], _, hb, _, hf =>
      have hx := hb x (by simp)
      have hy := hb y (by simp)
      rw [enc85A_short fs [x, y] fe (by simp) (by simp), wordOf_2, digits85_eq] at hf ⊢
      simp only [List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero, Nat.zero_add] at hf ⊢
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 6 := ⟨f - 6, by omega⟩
      generalize hw : x * 16777216 + y * 65536 = w at *
      have hb1 : w ≤ 4294901760 := by omega
      have e1 := d3 w (by omega)
      have e2 : 0 + 1 + 1 + 1 + 1 = 4 := rfl
      rw [s0, a85_d ig fs (g + 5) _ _ 0 0 false o _ _ (hg _) (Nat.mod_lt _ (by decide)) (by omega) (by omega),
        a85_d ig fs (g + 4) _ _ _ _ false o _ _ (hg _) (Nat.mod_lt _ (by decide)) (by omega) (by omega),
        a85_d ig fs (g + 3) _ _ _ _ false o _ _ (hg _) (Nat.mod_lt _ (by decide)) (by omega) (by omega), e1,
        a85_n ig fs (g + 2) _ _ false o _ (by omega) (by omega), e2,
        a85_n5 ig fs (g + 1) _ 2 false o _ (by omega) (by decide) (by decide) (by rw [pad2]; omega),
        a85_end ig fs g _ _ (by omega), pad2, ← hw, cut2 x y _ hx hy (by omega)]
    | [x, y, z], _, hb, _, hf =>
      have hx := hb x (by simp)
      have hy := hb y (by simp)
      have hz := hb z (by simp)
      rw [enc85A_short fs [x, y, z] fe (by simp) (by simp), wordOf_3, digits85_eq] at hf ⊢
      simp only [List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero, Nat.zero_add] at hf ⊢
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 6 := ⟨f - 6, by omega⟩
      generalize hw : x * 16777216 + y * 65536 + z * 256 = w at *
      have hb1 : w ≤ 4294967040 := by omega
      have e1 := d4 w (by omega)
      have e2 : 0 + 1 + 1 + 1 + 1 = 4 := rfl
      rw [s0, a85_d ig fs (g + 5) _ _ 0 0 false o _ _ (hg _) (Nat.mod_lt _ (by decide)) (by omega) (by omega),
        a85_d ig fs (g + 4) _ _ _ _ false o _ _ (hg _) (Nat.mod_lt _ (by decide)) (by omega) (by omega),
        a85_d ig fs (g + 3) _ _ _ _ false o _ _ (hg _) (Nat.mod_lt _ (by decide)) (by omega) (by omega),
        a85_d ig fs (g + 2) _ _ _ _ false o _ _ (hg _) (Nat.mod_lt _ (by decide)) (by omega) (by omega), e1, e2,
        a85_n5 ig fs (g + 1) _ 3 false o _ (by omega) (by decide) (by decide) (by rw [pad1]; omega),
        a85_end ig fs g _ _ (by omega), pad1, ← hw, cut3 x y z _ hx hy hz (by omega)]
    | x :: y :: z :: e :: r, h, hb, hfe, hf =>
      have hx := hb x (by simp)
      have hy := hb y (by simp)
      have hz := hb z (by simp)
      have he := hb e (by simp)
      obtain ⟨fe, rfl⟩ : ∃ k, fe = k + 1 := ⟨fe - 1, by simp only [List.length_cons] at hfe; omega⟩
      have hbytes : ∀ w, w = x * 16777216 + y * 65536 + z * 256 + e → word4 w 4 = [x, y, z, e] := by
        intro w hw
        rw [word4_4]
        simp only [List.cons.injEq, and_true]
        refine ⟨by omega, by omega, by omega, by omega⟩
      have hr := ih r (by simp only [List.length_cons] at h; omega) (fun y hy => hb y (by simp [hy])) fe
      have hl : r.length ≤ fe := by simp only [List.length_cons] at hfe; omega
      rw [enc85A_4] at hf ⊢
      rw [wordOf_4] at hf ⊢
      generalize hw : x * 16777216 + y * 65536 + z * 256 + e = w at *
      have hwb := hbytes w rfl
      have happ : o ++ [x, y, z, e] ++ r = o ++ x :: y :: z :: e :: r := by simp
      by_cases h0 : w = 0
      · have e0 : (w == 0) = true := by simpa using h0
        simp only [e0, if_true, List.cons_append, List.nil_append, List.length_cons] at hf ⊢
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
        rw [a85_fold ig fs g 122 o _ _ (by omega) (Or.inl rfl)]
        have : (if (122 == 121) = true then 0x20202020 else 0) = w := by simp [h0]
        rw [this, hwb, ← happ]
        have e3 : ((enc85A fs fe r).length : Int) + 1 - 1 = (enc85A fs fe r).length := by omega
        push_cast
        rw [e3]
        exact hr g _ hl (by omega)
      · have e0 : (w == 0) = false := by simpa using h0
        by_cases h1 : (fs && w == 0x20202020) = true
        · simp only [e0, Bool.false_eq_true, if_false, h1, if_true, List.cons_append, List.nil_append, List.length_cons]
            at hf ⊢
          obtain ⟨hfs, h20⟩ : fs = true ∧ w = 0x20202020 := by simpa using h1
          obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
          rw [a85_fold ig fs g 121 o _ _ (by omega) (Or.inr ⟨rfl, hfs⟩)]
          have : (if (121 == 121) = true then 0x20202020 else 0) = w := by simp [h20]
          rw [this, hwb, ← happ]
          have e3 : ((enc85A fs fe r).length : Int) + 1 - 1 = (enc85A fs fe r).length := by omega
          push_cast
          rw [e3]
          exact hr g _ hl (by omega)
        · simp only [e0, Bool.false_eq_true, if_false, h1] at hf ⊢
          have hlenD : (digits85 a85Alpha w).length = 5 := rfl
          rw [List.length_append, hlenD] at hf ⊢
          obtain ⟨g, rfl⟩ : ∃ g, f = g + 5 := ⟨f - 5, by omega⟩
          rw [a85_group ig fs g w o _ _ (by omega) (by push_cast; omega), hwb, ← happ]
          exact hr g _ hl (by omega)

/-- `a85decode(a85encode(d, foldspaces=f), foldspaces=f) == d`, through the `z` and `y` folds and a cut
last group. -/
def A85RoundTripC : Prop :=
  ∀ (d out : List Nat) (f : Bool), (∀ x ∈ d, x < 256) → b2aA85 (.bytes d) f 0 false false = .ok out →
    a2bA85 (.bytes out) f false (.bytes a85Ignore) false = .ok d

theorem a85RoundTripC_proven : A85RoundTripC := by
  intro d out f hd h
  have h1 : out = enc85A f d.length d := by
    simp [b2aA85, bufData, sizeT, b2aA85Core, enc85A, bind, Except.bind, pure, Except.pure] at h
    exact h.symm
  subst h1
  have := dec85A_main a85Ignore f d.length d (Nat.le_refl _) hd d.length _ [] (Nat.le_refl _) (Nat.le_refl _)
  simp [a2bA85, a2bA85Core, asciiBuffer, bufData, bind, Except.bind, pure, Except.pure, this]

/-! ### `ignorechars` and `wraplines` -/

theorem ign_of (g : List Nat) (c : Nat) : ign (if g.isEmpty then none else some g) c = g.contains c := by
  cases g <;> simp [ign]

/-- What `ignorechars` leaves of the input. -/
def keepHex (g : List Nat) (c : Nat) : Bool := !(decide (digitValue c ≥ 16) && g.contains c)

theorem hexIg_cons (ig : Option (List Nat)) (c : Nat) (cs : List Nat) (pair : Option Nat) (out : List Nat) :
    a2bHexIg ig (c :: cs) pair out =
      if digitValue c ≥ 16 then
        if !ign ig c then .error (err "Non-hexadecimal digit found") else a2bHexIg ig cs pair out
      else
        match pair with
        | none => a2bHexIg ig cs (some (digitValue c)) out
        | some l => a2bHexIg ig cs none (out ++ [l * 16 + digitValue c]) := by
  cases pair <;> rfl

theorem hexIg_filter (g : List Nat) : ∀ (s : List Nat) (pair : Option Nat) (out : List Nat),
    a2bHexIg (if g.isEmpty then none else some g) s pair out = a2bHexIg none (s.filter (keepHex g)) pair out := by
  intro s
  induction s with
  | nil => intro pair _; cases pair <;> rfl
  | cons c r ih =>
    intro pair out
    have hi := ign_of g c
    by_cases h16 : digitValue c ≥ 16
    · cases hg : g.contains c with
      | true =>
        have hf : keepHex g c = false := by simp only [keepHex, decide_eq_true h16, hg, Bool.true_and, Bool.not_true]
        rw [List.filter_cons_of_neg (by rw [hf]; exact Bool.false_ne_true), hexIg_cons]
        simp only [if_pos h16, hi, hg, Bool.not_true, Bool.false_eq_true, if_false]
        exact ih _ _
      | false =>
        have hf : keepHex g c = true := by simp only [keepHex, hg, Bool.and_false, Bool.not_false]
        rw [List.filter_cons_of_pos hf, hexIg_cons, hexIg_cons]
        rw [if_pos h16, if_pos h16, hi, hg]
        simp [ign]
    · have hf : keepHex g c = true := by simp only [keepHex, decide_eq_false h16, Bool.false_and, Bool.not_false]
      rw [List.filter_cons_of_pos hf, hexIg_cons, hexIg_cons]
      simp only [if_neg h16]
      split
      · exact ih _ _
      · exact ih _ _

/-- `unhexlify(s, ignorechars=g)` is `unhexlify` of `s` without the bytes of `g`, leaving out only those
that are not hexadecimal digits: a digit named in `ignorechars` is still a digit. That covers every
result, the failures with their messages included. -/
def HexIgnoreLaw : Prop :=
  ∀ s g : List Nat, a2bHexI (.bytes s) (.bytes g) = a2bHexI (.bytes (s.filter (keepHex g))) (.bytes [])

theorem hexIgnoreLaw_proven : HexIgnoreLaw := by
  intro s g
  simp only [a2bHexI, asciiBuffer, bufData, bind, Except.bind]
  rw [hexIg_filter g s none []]
  rfl

/-- The lines of a wrapped output, with the newlines `wraplines` puts between them. -/
def joinNl : List (List Nat) → List Nat
  | [] => []
  | [l] => l
  | l :: r => l ++ [10] ++ joinNl r

theorem wrap_lines (w : Nat) (hw : 0 < w) : ∀ (f : Nat) (s : List Nat), s.length ≤ f →
    ∃ ls : List (List Nat), ls ≠ [] ∧ wraplines w f s = joinNl ls ∧ ls.flatten = s ∧
      (∀ l ∈ ls.dropLast, l.length = w) ∧ ∀ l ∈ ls, l.length ≤ w := by
  intro f
  induction f with
  | zero =>
    intro s h
    have : s = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact ⟨[[]], by simp, rfl, rfl, by simp, by simp⟩
  | succ f ih =>
    intro s h
    by_cases hl : s.length ≤ w
    · refine ⟨[s], by simp, ?_, by simp, by simp, by simpa using hl⟩
      rw [wraplines, if_pos hl]
      rfl
    · obtain ⟨ls, h1, h2, h3, h4, h5⟩ := ih (s.drop w) (by simp only [List.length_drop]; omega)
      have ht : (s.take w).length = w := by simp only [List.length_take]; omega
      refine ⟨s.take w :: ls, by simp, ?_, ?_, ?_, ?_⟩
      · rw [wraplines, if_neg hl, h2]
        cases ls with
        | nil => exact absurd rfl h1
        | cons a b => rfl
      · simp only [List.flatten_cons, h3, List.take_append_drop]
      · intro l hm
        cases ls with
        | nil => exact absurd rfl h1
        | cons a b =>
          simp only [List.dropLast_cons₂, List.mem_cons] at hm
          rcases hm with rfl | hm
          · exact ht
          · exact h4 l hm
      · intro l hm
        rcases List.mem_cons.mp hm with rfl | hm
        · omega
        · exact h5 l hm

/-- What `wraplines` does, for any width and any contents: it cuts the data into lines joined by one
newline, each of them `width` long but the last, which is not empty unless the data is and holds at
most `width`. No newline ends the output. The callers do not call it with a width of zero. -/
def WraplinesLaw : Prop :=
  ∀ (w : Nat) (s : List Nat), 0 < w →
    ∃ ls : List (List Nat), ls ≠ [] ∧ wraplines w s.length s = joinNl ls ∧ ls.flatten = s ∧
      (∀ l ∈ ls.dropLast, l.length = w) ∧ ∀ l ∈ ls, l.length ≤ w

theorem wraplinesLaw_proven : WraplinesLaw :=
  fun w s hw => wrap_lines w hw s.length s (Nat.le_refl _)

/-- The same with any `wrapcol` and with the Adobe framing. -/
def A85WrapRoundTripC : Prop :=
  ∀ (d out : List Nat) (f adobe : Bool) (w : Int), (∀ x ∈ d, x < 256) → b2aA85 (.bytes d) f w false adobe = .ok out →
    a2bA85 (.bytes out) f adobe (.bytes a85Ignore) false = .ok d

end PyLean.TextLibs.Binascii
