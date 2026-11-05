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

end PyLean.TextLibs.Binascii
