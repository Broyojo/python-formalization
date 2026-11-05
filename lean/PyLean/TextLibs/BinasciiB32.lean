import PyLean.TextLibs.BinasciiB64b

/-!
`binascii.a2b_base32` and `binascii.b2a_base32` of 3.15.2 over every option: `padded`, `alphabet`,
`ignorechars`, `canonical` and `wrapcol`. As for base64, the fast path is taken out of the decoder first:
`slow32` is the slow loop alone, with the `goto fastpath` of `Modules/binascii.c:1810` kept as what it does
to the state (the `pads = 0` of the re-declaration at `:1713`).
-/

namespace PyLean.TextLibs.Binascii

open PyLean

set_option linter.unusedSimpArgs false

/-- The slow loop of `binascii_a2b_base32_impl`, `Modules/binascii.c:1712-1818`, to the end of the
input. After the eighth character the C code jumps back to the fast path, which declares `pads` again,
so it is 0 from there. -/
def slow32 (t : Nat → Nat) (padded : Bool) (ig : Option (List Nat)) : List Nat → Dec32 → Py Dec32
  | [], st => .ok st
  | x :: xs, st =>
    if padded && x == 61 then
      let pads := st.pads + 1
      let st' := { st with pads }
      if (st.octa == 2 || st.octa == 4 || st.octa == 5 || st.octa == 7) && decide (st.octa + pads ≤ 8) then
        slow32 t padded ig xs st'
      else if ign ig 61 then slow32 t padded ig xs st'
      else if st.octa == 1 || st.octa == 3 || st.octa == 6 then .ok st'
      else .error (err (if st.octa = 0 ∧ st.out.isEmpty then "Leading padding not allowed"
                        else "Excess padding not allowed"))
    else
      let v := t x
      if v ≥ 32 then
        if !ign ig x then
          .error (err (if x = 61 then "Padding not allowed" else "Only base32 data is allowed"))
        else slow32 t padded ig xs st
      else if st.pads ≠ 0 ∧ !ign ig 61 then
        .error (err (if st.octa + st.pads = 8 then "Excess data after padding"
                     else "Discontinuous padding not allowed"))
      else
        let st' := decStep32 st v
        if st.octa = 7 then slow32 t padded ig xs { st' with pads := 0 }
        else slow32 t padded ig xs st'

/-- The checks after the loop, `Modules/binascii.c:1820-1849`. -/
def fin32 (padded canonical : Bool) (st : Dec32) : Py (List Nat) := do
  if st.octa == 1 || st.octa == 3 || st.octa == 6 then
    throw (err s!"Invalid base32-encoded string: number of data characters \
      ({st.out.length / 5 * 8 + st.octa}) cannot be 1, 3, or 6 more than a multiple of 8")
  if padded ∧ st.octa ≠ 0 ∧ st.octa + st.pads < 8 then throw (err "Incorrect padding")
  if canonical ∧ st.left ≠ 0 then throw (err "Non-zero padding bits")
  return st.out

theorem slow32_data (t : Nat → Nat) (p : Bool) (ig : Option (List Nat)) (x : Nat) (xs : List Nat) (st : Dec32)
    (hx : t x < 32) (h61 : 32 ≤ t 61) (hp : st.pads = 0) :
    slow32 t p ig (x :: xs) st = slow32 t p ig xs (decStep32 st (t x)) := by
  have hne : (x == 61) = false := by
    apply beq_false_of_ne; intro e; subst e; omega
  have hd : { decStep32 st (t x) with pads := 0 } = decStep32 st (t x) := by
    have := dec32_pads st (t x)
    rw [hp] at this
    cases h : decStep32 st (t x)
    simp_all
  simp only [slow32, hne, Bool.and_false, Bool.false_eq_true, if_false, if_neg (Nat.not_le.mpr hx), hp, ne_eq,
    not_true_eq_false, false_and]
  split
  · rw [hd]
  · rfl

/-- Eight turns of the slow loop from a clean position. -/
theorem dec32_group8 (v0 v1 v2 v3 v4 v5 v6 v7 : Nat) (out : List Nat) (h0 : v0 < 32) (h1 : v1 < 32) (h2 : v2 < 32)
    (h3 : v3 < 32) (h4 : v4 < 32) (h5 : v5 < 32) (h6 : v6 < 32) (h7 : v7 < 32) :
    decStep32 (decStep32 (decStep32 (decStep32 (decStep32 (decStep32 (decStep32 (decStep32 ⟨0, 0, 0, out⟩ v0) v1) v2)
      v3) v4) v5) v6) v7 =
      ⟨0, 0, 0, out ++ [(v0 * 8 + v1 / 4) % 256, (v1 * 64 + v2 * 2 + v3 / 16) % 256, (v3 * 16 + v4 / 2) % 256,
        (v4 * 128 + v5 * 4 + v6 / 8) % 256, (v6 * 32 + v7) % 256]⟩ := by
  simp only [decStep32, List.append_assoc, List.cons_append, List.nil_append, Dec32.mk.injEq, true_and,
    List.append_cancel_left_eq, List.cons.injEq, and_true]
  refine ⟨by omega, by omega, by omega, by omega⟩

theorem slow32_octa (t : Nat → Nat) (p : Bool) (ig : Option (List Nat)) (h61 : 32 ≤ t 61) (C r o out : List Nat)
    (hl : C.length = 8) (hq : octa32 t C = some o) :
    slow32 t p ig (C ++ r) ⟨0, 0, 0, out⟩ = slow32 t p ig r ⟨0, 0, 0, out ++ o⟩ := by
  match C, hl with
  | [c0, c1, c2, c3, c4, c5, c6, c7], _ =>
    simp only [octa32, List.map_cons, List.map_nil] at hq
    by_cases hn : [t c0, t c1, t c2, t c3, t c4, t c5, t c6, t c7].any (· ≥ 32) = true
    · rw [if_pos hn] at hq; cases hq
    · rw [if_neg hn] at hq
      simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, decide_eq_true_eq, not_or,
        Nat.not_le] at hn
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7⟩ := hn
      simp only [List.cons_append, List.nil_append]
      rw [slow32_data t p ig _ _ _ n0 h61 rfl, slow32_data t p ig _ _ _ n1 h61 (by rw [dec32_pads]),
        slow32_data t p ig _ _ _ n2 h61 (by rw [dec32_pads, dec32_pads]),
        slow32_data t p ig _ _ _ n3 h61 (by rw [dec32_pads, dec32_pads, dec32_pads]),
        slow32_data t p ig _ _ _ n4 h61 (by rw [dec32_pads, dec32_pads, dec32_pads, dec32_pads]),
        slow32_data t p ig _ _ _ n5 h61 (by rw [dec32_pads, dec32_pads, dec32_pads, dec32_pads, dec32_pads]),
        slow32_data t p ig _ _ _ n6 h61 (by rw [dec32_pads, dec32_pads, dec32_pads, dec32_pads, dec32_pads, dec32_pads]),
        slow32_data t p ig _ _ _ n7 h61
          (by rw [dec32_pads, dec32_pads, dec32_pads, dec32_pads, dec32_pads, dec32_pads, dec32_pads]),
        dec32_group8 _ _ _ _ _ _ _ _ out n0 n1 n2 n3 n4 n5 n6 n7]
      simp only [Option.some.injEq] at hq
      subst hq
      rfl

/-- `base32_decode_fast` can be taken out from a clean position. -/
theorem slow32_fast (t : Nat → Nat) (p : Bool) (ig : Option (List Nat)) (h61 : 32 ≤ t 61) :
    ∀ (n : Nat) (s out : List Nat),
      slow32 t p ig s ⟨0, 0, 0, out⟩ = slow32 t p ig (fast32 t n s out).1 ⟨0, 0, 0, (fast32 t n s out).2⟩ := by
  intro n
  induction n with
  | zero => intro s out; rfl
  | succ n ih =>
    intro s out
    simp only [fast32]
    split
    · rename_i hl
      cases hq : octa32 t (s.take 8) with
      | none => rfl
      | some o =>
        simp only
        have := slow32_octa t p ig h61 (s.take 8) (s.drop 8) o out (by simp only [List.length_take]; omega) hq
        rw [List.take_append_drop] at this
        rw [this]
        exact ih _ _
    · rfl

theorem fast32_len (t : Nat → Nat) : ∀ (n : Nat) (s out : List Nat), (fast32 t n s out).1.length ≤ s.length := by
  intro n
  induction n with
  | zero => intro s out; exact Nat.le_refl _
  | succ n ih =>
    intro s out
    simp only [fast32]
    split
    · cases hq : octa32 t (s.take 8) with
      | none => exact Nat.le_refl _
      | some o =>
        simp only
        have := ih (s.drop 8) (out ++ o)
        simp only [List.length_drop] at this
        omega
    · exact Nat.le_refl _

/-- The loop with its `goto fastpath` is the slow loop alone. -/
theorem slow32_run (t : Nat → Nat) (p : Bool) (ig : Option (List Nat)) (h61 : 32 ≤ t 61) :
    ∀ (f : Nat) (s : List Nat) (st : Dec32), s.length < f → a2b32Run t p ig f s st = slow32 t p ig s st := by
  intro f
  induction f with
  | zero => intro _ _ h; omega
  | succ f ih =>
    intro s st h
    cases s with
    | nil => rfl
    | cons x xs =>
      have hl : xs.length < f := by simpa using h
      simp only [a2b32Run, slow32]
      split
      · split
        · exact ih _ _ hl
        · split
          · exact ih _ _ hl
          · rfl
      · split
        · split
          · rfl
          · exact ih _ _ hl
        · split
          · rfl
          · split
            · rename_i h7
              obtain ⟨q, pp, l, o⟩ := st
              simp only at h7
              subst h7
              rw [ih _ _ (by have := fast32_len t xs.length xs (decStep32 ⟨7, pp, l, o⟩ (t x)).out; omega)]
              simp only [decStep32]
              exact (slow32_fast t p ig h61 xs.length xs _).symm
            · exact ih _ _ hl

/-- `binascii_a2b_base32_impl` from the fast path on is the slow loop and the final checks. -/
theorem core32_slow (t : Nat → Nat) (p : Bool) (ig : Option (List Nat)) (h61 : 32 ≤ t 61) (k : Bool) (s : List Nat) :
    a2b32Core t p ig k s = (slow32 t p ig s {}).bind (fin32 p k) := by
  have hf := fast32_len t s.length s []
  have h1 : a2b32Run t p ig (s.length + 1) (fast32 t s.length s []).1 { out := (fast32 t s.length s []).2 } =
      slow32 t p ig s {} := by
    rw [slow32_run t p ig h61 _ _ _ (by omega)]
    exact (slow32_fast t p ig h61 s.length s []).symm
  simp only [a2b32Core]
  rw [h1]
  cases slow32 t p ig s {} with
  | error e => rfl
  | ok st => rfl

/-! ### Characters the loop skips -/

/-- The characters the loop passes over without a change of state: not in the alphabet, not the pad
character of a padded decode, and named by `ignorechars`. -/
def skip32 (t : Nat → Nat) (p : Bool) (ig : Option (List Nat)) (x : Nat) : Bool :=
  decide (t x ≥ 32) && !(p && x == 61) && ign ig x

theorem slow32_filter (t : Nat → Nat) (p : Bool) (ig : Option (List Nat)) : ∀ (s : List Nat) (st : Dec32),
    slow32 t p ig s st = slow32 t p ig (s.filter (fun x => !skip32 t p ig x)) st := by
  intro s
  induction s with
  | nil => intro st; rfl
  | cons x xs ih =>
    intro st
    by_cases hs : skip32 t p ig x = true
    · rw [List.filter_cons_of_neg (by simp [hs])]
      simp only [skip32, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hs
      obtain ⟨⟨h1, h2⟩, h3⟩ := hs
      simp only [slow32, h2, Bool.false_eq_true, if_false, if_pos h1, h3, Bool.not_true]
      exact ih st
    · rw [List.filter_cons_of_pos (by simpa using hs)]
      simp only [slow32]
      split
      · split
        · exact ih _
        · split
          · exact ih _
          · rfl
      · split
        · split
          · rfl
          · exact ih _
        · split
          · rfl
          · split
            · exact ih _
            · exact ih _

/-! ### Decoding what the encoder writes -/

/-- `pads` of `binascii_b2a_base32_impl`, `Modules/binascii.c:1903`. -/
def pads32 (n : Nat) : Nat := (5 - n % 5) % 5 * 8 / 5

/-- What the encoder writes before the padding, with `fe` as the fuel of its fast path. -/
def enc32B (a : List Nat) (fe : Nat) (d : List Nat) : List Nat :=
  (fastEnc32 a fe d).1 ++ tail32 a (fastEnc32 a fe d).2

theorem enc32S_B (a : List Nat) (fe : Nat) (d : List Nat) :
    enc32S a fe d = enc32B a fe d ++ List.replicate (pads32 d.length) 61 := rfl

theorem enc32B_nil (a : List Nat) (fe : Nat) : enc32B a fe [] = [] := by
  have := enc32S_nil a fe
  rw [enc32S_B] at this
  simpa [pads32] using this

theorem enc32B_short (a : List Nat) (fe : Nat) (d : List Nat) (h : d.length < 5) :
    enc32B a fe d = tail32 a d := by
  unfold enc32B
  rw [fe32_short a d fe h]
  rfl

theorem enc32B_5 (a : List Nat) (fe x1 x2 x3 x4 x5 : Nat) (r : List Nat) (V : Nat)
    (hV : V = x1 * 2 ^ 32 + x2 * 2 ^ 24 + x3 * 65536 + x4 * 256 + x5) :
    enc32B a (fe + 1) (x1 :: x2 :: x3 :: x4 :: x5 :: r) =
      [V / 2 ^ 35 % 32, V / 2 ^ 30 % 32, V / 2 ^ 25 % 32, V / 2 ^ 20 % 32, V / 2 ^ 15 % 32, V / 2 ^ 10 % 32,
       V / 2 ^ 5 % 32, V / 2 ^ 0 % 32].map (a.getD · 0) ++ enc32B a fe r := by
  have := enc32S_5 a fe x1 x2 x3 x4 x5 r V hV
  rw [enc32S_B, enc32S_B] at this
  have hp : pads32 (x1 :: x2 :: x3 :: x4 :: x5 :: r).length = pads32 r.length := by
    simp only [pads32, List.length_cons]
    have : (r.length + 1 + 1 + 1 + 1 + 1) % 5 = r.length % 5 := by omega
    rw [this]
  rw [hp, ← List.append_assoc] at this
  exact List.append_cancel_right this

theorem slow32_ds (a : List Nat) (t : Nat → Nat) (p : Bool) (ig : Option (List Nat))
    (ht : ∀ v, v < 32 → t (a.getD v 0) = v) (h61 : 32 ≤ t 61) :
    ∀ (vs : List Nat) (st : Dec32) (rest : List Nat), (∀ v ∈ vs, v < 32) → st.pads = 0 →
      slow32 t p ig (vs.map (a.getD · 0) ++ rest) st = slow32 t p ig rest (vs.foldl decStep32 st) := by
  intro vs
  induction vs with
  | nil => intro _ _ _ _; rfl
  | cons v r ih =>
    intro st rest hv hp
    have hl : v < 32 := hv v (by simp)
    rw [List.map_cons, List.cons_append, slow32_data t p ig _ _ st (by rw [ht v hl]; exact hl) h61 hp, ht v hl,
      ih _ rest (fun y hy => hv y (by simp [hy])) (by rw [dec32_pads, hp])]
    rfl

theorem slow32_ps (t : Nat → Nat) (ig : Option (List Nat)) : ∀ (n : Nat) (st : Dec32),
    (st.octa = 2 ∨ st.octa = 4 ∨ st.octa = 5 ∨ st.octa = 7) → st.octa + st.pads + n ≤ 8 →
    slow32 t true ig (List.replicate n 61) st = .ok { st with pads := st.pads + n } := by
  intro n
  induction n with
  | zero => intro st _ _; rfl
  | succ n ih =>
    intro st ho hp
    have hc : (st.octa == 2 || st.octa == 4 || st.octa == 5 || st.octa == 7) = true := by
      rcases ho with h | h | h | h <;> simp [h]
    have hd : st.octa + (st.pads + 1) ≤ 8 := by omega
    rw [List.replicate_succ]
    simp only [slow32, Bool.true_and, beq_self_eq_true, if_true, hc, decide_true, hd, Bool.and_self]
    have := ih { st with pads := st.pads + 1 } ho (by simp only; omega)
    rw [this]
    have e2 : st.pads + 1 + n = st.pads + (n + 1) := by omega
    simp only [e2]

/-- The alphabet facts the decoder needs: its table inverts it, and the pad is not data. -/
structure Inv32 (a : List Nat) (t : Nat → Nat) : Prop where
  ht : ∀ v, v < 32 → t (a.getD v 0) = v
  h61 : 32 ≤ t 61

theorem dec_tail32 (a : List Nat) (t : Nat → Nat) (hi : Inv32 a t) (p ig : _) (k : Bool) (vs : List Nat) (n : Nat)
    (out want : List Nat) (hv : ∀ v ∈ vs, v < 32) (hn : vs.length + n = 8)
    (hk : vs.length = 2 ∨ vs.length = 4 ∨ vs.length = 5 ∨ vs.length = 7)
    (hout : (vs.foldl decStep32 ⟨0, 0, 0, out⟩).out = want) (hleft : (vs.foldl decStep32 ⟨0, 0, 0, out⟩).left = 0) :
    ∃ st, slow32 t p ig (vs.map (a.getD · 0) ++ List.replicate (if p then n else 0) 61) ⟨0, 0, 0, out⟩ = .ok st ∧
      fin32 p k st = .ok want := by
  rw [slow32_ds a t p ig hi.ht hi.h61 vs _ _ hv rfl]
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
  have h1 := ho vs ⟨0, 0, 0, out⟩ (by simp only; omega)
  simp only [Nat.zero_add] at h1
  have h2 := hp vs ⟨0, 0, 0, out⟩
  generalize hF : vs.foldl decStep32 ⟨0, 0, 0, out⟩ = F at h1 h2 hout hleft
  have hc : ¬ ((F.octa == 1 || F.octa == 3 || F.octa == 6) = true) := by
    rw [h1]; rcases hk with h | h | h | h <;> simp [h]
  cases p with
  | true =>
    simp only [if_true]
    rw [slow32_ps t ig n F (by rw [h1]; exact hk) (by rw [h1, h2]; simp only; omega)]
    refine ⟨_, rfl, ?_⟩
    simp only [fin32, bind, Except.bind, pure, Except.pure, hc, if_false]
    have h3 : F.octa + (F.pads + n) = 8 := by rw [h1, h2]; simp only; omega
    simp [h3, hleft, hout]
  | false =>
    simp only [Bool.false_eq_true, if_false, List.replicate_zero]
    refine ⟨_, rfl, ?_⟩
    simp only [fin32, bind, Except.bind, pure, Except.pure, hc, if_false]
    simp [hleft, hout]

theorem octa_of_enc (a : List Nat) (t : Nat → Nat) (hi : Inv32 a t) (x1 x2 x3 x4 x5 V : Nat) (b1 : x1 < 256)
    (b2 : x2 < 256) (b3 : x3 < 256) (b4 : x4 < 256) (b5 : x5 < 256)
    (hV : V = x1 * 2 ^ 32 + x2 * 2 ^ 24 + x3 * 65536 + x4 * 256 + x5) :
    octa32 t ([V / 2 ^ 35 % 32, V / 2 ^ 30 % 32, V / 2 ^ 25 % 32, V / 2 ^ 20 % 32, V / 2 ^ 15 % 32,
        V / 2 ^ 10 % 32, V / 2 ^ 5 % 32, V / 2 ^ 0 % 32].map (a.getD · 0)) = some [x1, x2, x3, x4, x5] := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := t5 x1 x2 x3 x4 x5 V b1 b2 b3 b4 b5 hV
  rw [e0, e1, e2, e3, e4, e5, e6, e7]
  have hO := octa32_vals a t hi.ht (x1 / 8) (x1 % 8 * 4 + x2 / 64) (x2 / 2 % 32) (x2 % 2 * 16 + x3 / 16)
    (x3 % 16 * 2 + x4 / 128) (x4 / 4 % 32) (x4 % 4 * 8 + x5 / 32) (x5 % 32) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [bytes5 x1 x2 x3 x4 x5 b1 b2 b3 b4 b5] at hO
  exact hO

theorem fold_t1 (x : Nat) (out : List Nat) (hx : x < 256) :
    [x / 8, x % 8 * 4].foldl decStep32 ⟨0, 0, 0, out⟩ = ⟨2, 0, 0, out ++ [x]⟩ := by
  simp only [List.foldl_cons, List.foldl_nil, decStep32, Dec32.mk.injEq, List.append_cancel_left_eq,
    List.cons.injEq, and_true, true_and]
  omega

theorem fold_t2 (x y : Nat) (out : List Nat) (hx : x < 256) (hy : y < 256) :
    [x / 8, x % 8 * 4 + y / 64, y / 2 % 32, y % 2 * 16].foldl decStep32 ⟨0, 0, 0, out⟩ = ⟨4, 0, 0, out ++ [x, y]⟩ := by
  simp only [List.foldl_cons, List.foldl_nil, decStep32, Dec32.mk.injEq, List.append_assoc, List.cons_append,
    List.nil_append, List.append_cancel_left_eq, List.cons.injEq, and_true, true_and]
  omega

theorem fold_t3 (x y z : Nat) (out : List Nat) (hx : x < 256) (hy : y < 256) (hz : z < 256) :
    [x / 8, x % 8 * 4 + y / 64, y / 2 % 32, y % 2 * 16 + z / 16, z % 16 * 2].foldl decStep32 ⟨0, 0, 0, out⟩ =
      ⟨5, 0, 0, out ++ [x, y, z]⟩ := by
  simp only [List.foldl_cons, List.foldl_nil, decStep32, Dec32.mk.injEq, List.append_assoc, List.cons_append,
    List.nil_append, List.append_cancel_left_eq, List.cons.injEq, and_true, true_and]
  omega

theorem fold_t4 (x y z w : Nat) (out : List Nat) (hx : x < 256) (hy : y < 256) (hz : z < 256) (hw : w < 256) :
    [x / 8, x % 8 * 4 + y / 64, y / 2 % 32, y % 2 * 16 + z / 16, z % 16 * 2 + w / 128, w / 4 % 32,
      w % 4 * 8].foldl decStep32 ⟨0, 0, 0, out⟩ = ⟨7, 0, 0, out ++ [x, y, z, w]⟩ := by
  simp only [List.foldl_cons, List.foldl_nil, decStep32, Dec32.mk.injEq, List.append_assoc, List.cons_append,
    List.nil_append, List.append_cancel_left_eq, List.cons.injEq, and_true, true_and]
  omega

theorem dec_enc32 (a : List Nat) (t : Nat → Nat) (hi : Inv32 a t) (p : Bool) (ig : Option (List Nat)) (k : Bool) :
    ∀ (n : Nat) (d : List Nat), d.length ≤ n → (∀ x ∈ d, x < 256) → ∀ (fe : Nat) (out : List Nat), d.length ≤ fe →
      ∃ st, slow32 t p ig (enc32B a fe d ++ List.replicate (if p then pads32 d.length else 0) 61) ⟨0, 0, 0, out⟩ = .ok st ∧
        fin32 p k st = .ok (out ++ d) := by
  intro n
  induction n with
  | zero =>
    intro d h _ fe out _
    have : d = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [enc32B_nil]
    refine ⟨⟨0, 0, 0, out⟩, by cases p <;> rfl, ?_⟩
    simp [fin32, bind, Except.bind, pure, Except.pure]
  | succ n ih =>
    intro d h hb fe out hfe
    match d, h, hb, hfe with
    | [], _, _, _ =>
      rw [enc32B_nil]
      refine ⟨⟨0, 0, 0, out⟩, by cases p <;> rfl, ?_⟩
      simp [fin32, bind, Except.bind, pure, Except.pure]
    | [x], _, hb, _ =>
      have hx := hb x (by simp)
      rw [enc32B_short a fe [x] (by simp)]
      have e : tail32 a [x] = [x / 8, x % 8 * 4].map (a.getD · 0) := by
        simp only [tail32, List.map_cons, List.map_nil]
        rw [show x / 2 ^ 3 % 32 = x / 8 by omega, show x * 4 % 32 = x % 8 * 4 by omega]
      rw [e]
      have hf := fold_t1 x out hx
      rw [show pads32 [x].length = 6 by simp [pads32]]
      exact dec_tail32 a t hi p ig k [x / 8, x % 8 * 4] 6 out (out ++ [x]) (by intro v hv; simp at hv; omega) rfl (by simp)
        (by rw [hf]) (by rw [hf])
    | [x, y], _, hb, _ =>
      have hx := hb x (by simp)
      have hy := hb y (by simp)
      rw [enc32B_short a fe [x, y] (by simp)]
      obtain ⟨e0, e1, e2, e3⟩ := t2 x y hx hy
      have e : tail32 a [x, y] = [x / 8, x % 8 * 4 + y / 64, y / 2 % 32, y % 2 * 16].map (a.getD · 0) := by
        simp only [tail32, List.map_cons, List.map_nil]
        rw [e0, e1, e2, e3]
      rw [e]
      have hf := fold_t2 x y out hx hy
      rw [show pads32 [x, y].length = 4 by simp [pads32]]
      exact dec_tail32 a t hi p ig k [x / 8, x % 8 * 4 + y / 64, y / 2 % 32, y % 2 * 16] 4 out (out ++ [x, y]) (by intro v hv; simp at hv; omega) rfl (by simp)
        (by rw [hf]) (by rw [hf])
    | [x, y, z], _, hb, _ =>
      have hx := hb x (by simp)
      have hy := hb y (by simp)
      have hz := hb z (by simp)
      rw [enc32B_short a fe [x, y, z] (by simp)]
      obtain ⟨e0, e1, e2, e3, e4⟩ := t3 x y z hx hy hz
      have e : tail32 a [x, y, z] =
          [x / 8, x % 8 * 4 + y / 64, y / 2 % 32, y % 2 * 16 + z / 16, z % 16 * 2].map (a.getD · 0) := by
        simp only [tail32, List.map_cons, List.map_nil]
        rw [e0, e1, e2, e3, e4]
      rw [e]
      have hf := fold_t3 x y z out hx hy hz
      rw [show pads32 [x, y, z].length = 3 by simp [pads32]]
      exact dec_tail32 a t hi p ig k [x / 8, x % 8 * 4 + y / 64, y / 2 % 32, y % 2 * 16 + z / 16, z % 16 * 2] 3 out
        (out ++ [x, y, z]) (by intro v hv; simp at hv; omega) rfl (by simp)
        (by rw [hf]) (by rw [hf])
    | [x, y, z, w], _, hb, _ =>
      have hx := hb x (by simp)
      have hy := hb y (by simp)
      have hz := hb z (by simp)
      have hw := hb w (by simp)
      rw [enc32B_short a fe [x, y, z, w] (by simp)]
      obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := t4 x y z w hx hy hz hw
      have e : tail32 a [x, y, z, w] =
          [x / 8, x % 8 * 4 + y / 64, y / 2 % 32, y % 2 * 16 + z / 16, z % 16 * 2 + w / 128, w / 4 % 32,
            w % 4 * 8].map (a.getD · 0) := by
        simp only [tail32, List.map_cons, List.map_nil]
        rw [e0, e1, e2, e3, e4, e5, e6]
      rw [e]
      have hf := fold_t4 x y z w out hx hy hz hw
      rw [show pads32 [x, y, z, w].length = 1 by simp [pads32]]
      exact dec_tail32 a t hi p ig k [x / 8, x % 8 * 4 + y / 64, y / 2 % 32, y % 2 * 16 + z / 16, z % 16 * 2 + w / 128,
        w / 4 % 32, w % 4 * 8] 1 out (out ++ [x, y, z, w]) (by intro v hv; simp at hv; omega) rfl (by simp)
        (by rw [hf]) (by rw [hf])
    | x1 :: x2 :: x3 :: x4 :: x5 :: r, h, hb, hfe =>
      have b1 := hb x1 (by simp)
      have b2 := hb x2 (by simp)
      have b3 := hb x3 (by simp)
      have b4 := hb x4 (by simp)
      have b5 := hb x5 (by simp)
      obtain ⟨fe, rfl⟩ : ∃ k, fe = k + 1 := ⟨fe - 1, by simp only [List.length_cons] at hfe; omega⟩
      generalize hV : x1 * 2 ^ 32 + x2 * 2 ^ 24 + x3 * 65536 + x4 * 256 + x5 = V
      rw [enc32B_5 a fe x1 x2 x3 x4 x5 r V hV.symm]
      have hp : pads32 (x1 :: x2 :: x3 :: x4 :: x5 :: r).length = pads32 r.length := by
        simp only [pads32, List.length_cons]
        have : (r.length + 1 + 1 + 1 + 1 + 1) % 5 = r.length % 5 := by omega
        rw [this]
      rw [hp, List.append_assoc,
        slow32_octa t p ig hi.h61 _ _ _ out (by simp) (octa_of_enc a t hi x1 x2 x3 x4 x5 V b1 b2 b3 b4 b5 hV.symm)]
      obtain ⟨st, h1, h2⟩ := ih r (by simp only [List.length_cons] at h; omega) (fun y hy => hb y (by simp [hy])) fe
        (out ++ [x1, x2, x3, x4, x5]) (by simp only [List.length_cons] at hfe; omega)
      refine ⟨st, h1, ?_⟩
      simpa [List.append_assoc] using h2

end PyLean.TextLibs.Binascii
