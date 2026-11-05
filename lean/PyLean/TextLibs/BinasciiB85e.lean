import PyLean.TextLibs.BinasciiB85d

/-!
`binascii.b2a_base85` over every option.
-/

namespace PyLean.TextLibs.Binascii

open PyLean

set_option linter.unusedSimpArgs false

/-- `bytes.translate(bytes.maketrans(BASE85_ALPHABET, a))` on one byte. -/
def tr85 (A : List Nat) (c : Nat) : Nat := if c ∈ b85Alpha then A.getD (b85Alpha.idxOf c) 0 else c

theorem b85_idx : ∀ v, v < 85 → b85Alpha.idxOf (b85Alpha.getD v 0) = v ∧ b85Alpha.getD v 0 ∈ b85Alpha := by
  decide +kernel

theorem digits85_tr (A : List Nat) (w : Nat) : digits85 A w = (digits85 b85Alpha w).map (tr85 A) := by
  simp only [digits85, List.map_map]
  apply List.map_congr_left
  intro i _
  obtain ⟨h1, h2⟩ := b85_idx (w / 85 ^ (4 - i) % 85) (Nat.mod_lt _ (by decide))
  simp only [Function.comp, tr85, if_pos h2, h1]

theorem enc85P_tr (A : List Nat) (pad : Bool) : ∀ (fe : Nat) (d : List Nat),
    enc85P A fe d pad = (enc85P b85Alpha fe d pad).map (tr85 A) := by
  intro fe
  induction fe with
  | zero =>
    intro d
    unfold enc85P
    rw [show fullB85 A 0 d = ([], d) from rfl, show fullB85 b85Alpha 0 d = ([], d) from rfl]
    simp only [List.nil_append]
    split
    · rfl
    · rw [digits85_tr, List.map_take]
  | succ fe ih =>
    intro d
    by_cases hl : d.length ≥ 4
    · obtain ⟨p, q, r, e, t, rfl⟩ : ∃ p q r e t, d = p :: q :: r :: e :: t := by
        match d, hl with
        | p :: q :: r :: e :: t, _ => exact ⟨p, q, r, e, t, rfl⟩
      rw [enc85P_4, enc85P_4, ih, digits85_tr, List.map_append]
    · by_cases hd : d = []
      · subst hd; rw [enc85P_nil, enc85P_nil]; rfl
      · rw [enc85P_short A d _ pad (by omega) hd, enc85P_short b85Alpha d _ pad (by omega) hd, digits85_tr, List.map_take]

theorem wordOf_pad (d : List Nat) (h : d.length < 4) : wordOf d = wordOf (d ++ zeros85 d true) := by
  simp only [zeros85, if_true]
  have e : (d ++ List.replicate ((4 - d.length % 4) % 4) 0).length = 4 ∨ d.length = 0 := by
    simp only [List.length_append, List.length_replicate]; omega
  rcases e with e | e
  · unfold wordOf
    rw [e, show 4 - 4 = 0 from rfl, List.replicate_zero, List.append_nil]
    simp only [List.length_append, List.length_replicate] at e
    have : (4 - d.length % 4) % 4 = 4 - d.length := by omega
    rw [this]
  · have : d = [] := List.eq_nil_of_length_eq_zero e
    subst this
    rfl

/-- `pad=True` writes what `pad=False` writes for the data with the zero bytes added. -/
theorem enc85P_padded (A : List Nat) : ∀ (fe : Nat) (d : List Nat), d.length ≤ fe →
    enc85P A fe d true = enc85P A (fe + 1) (d ++ zeros85 d true) false := by
  intro fe
  induction fe with
  | zero =>
    intro d h
    have : d = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [enc85P_nil]
    simp [zeros85, enc85P_nil]
  | succ fe ih =>
    intro d h
    by_cases hl : d.length ≥ 4
    · obtain ⟨p, q, r, e, t, rfl⟩ : ∃ p q r e t, d = p :: q :: r :: e :: t := by
        match d, hl with
        | p :: q :: r :: e :: t, _ => exact ⟨p, q, r, e, t, rfl⟩
      have hz : zeros85 (p :: q :: r :: e :: t) true = zeros85 t true := by
        simp only [zeros85, if_true, List.length_cons]
        have : (t.length + 1 + 1 + 1 + 1) % 4 = t.length % 4 := by omega
        rw [this]
      rw [enc85P_4, hz, show p :: q :: r :: e :: t ++ zeros85 t true = p :: q :: r :: e :: (t ++ zeros85 t true) from rfl,
        enc85P_4, ih t (by simp at h; omega)]
    · by_cases hd : d = []
      · subst hd; simp [zeros85, enc85P_nil]
      · rw [enc85P_short A d _ true (by omega) hd]
        have hlen : (d ++ zeros85 d true).length = 4 := by
          simp only [zeros85, if_true, List.length_append, List.length_replicate]
          have : 0 < d.length := List.length_pos_iff.mpr hd
          omega
        have hw := wordOf_pad d (by omega)
        simp only [if_true]
        rw [List.take_of_length_le (by simp [digits85]), hw]
        generalize d ++ zeros85 d true = D at hlen ⊢
        match D, hlen with
        | [p, q, r, e], _ => rw [enc85P_4, enc85P_nil, List.append_nil]

theorem enc85P_fuel (a : List Nat) (pad : Bool) : ∀ (n : Nat) (d : List Nat) (fe fe' : Nat), d.length ≤ n →
    d.length < 4 * fe + 4 → d.length < 4 * fe' + 4 → enc85P a fe d pad = enc85P a fe' d pad := by
  intro n
  induction n with
  | zero =>
    intro d fe fe' h _ _
    have : d = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [enc85P_nil, enc85P_nil]
  | succ n ih =>
    intro d fe fe' h h1 h2
    by_cases hl : d.length ≥ 4
    · obtain ⟨p, q, r, e, t, rfl⟩ : ∃ p q r e t, d = p :: q :: r :: e :: t := by
        match d, hl with
        | p :: q :: r :: e :: t, _ => exact ⟨p, q, r, e, t, rfl⟩
      obtain ⟨f1, rfl⟩ : ∃ k, fe = k + 1 := ⟨fe - 1, by simp at h1; omega⟩
      obtain ⟨f2, rfl⟩ : ∃ k, fe' = k + 1 := ⟨fe' - 1, by simp at h2; omega⟩
      rw [enc85P_4, enc85P_4, ih t f1 f2 (by simp at h; omega) (by simp at h1; omega) (by simp at h2; omega)]
    · by_cases hd : d = []
      · subst hd; rw [enc85P_nil, enc85P_nil]
      · rw [enc85P_short a d _ pad (by omega) hd, enc85P_short a d _ pad (by omega) hd]

/-- `b2a_base85` over every option, against its own output at the defaults (which `B85RoundTripAll`,
`B85StrictLaw` and `B85CanonicalLaw` pin through the decoder): `pad=True` writes what the defaults write
for the data with the zero bytes added (the docs: "the zero-padding applied to the end of the input is
retained"), `alphabet` is `translate` from the standard alphabet, and a non-zero `wrapcol` is rounded to a
multiple of 5 (at least 5) and the lines are cut by `wraplines`, unless the output is empty. Then the
refusals in their order: a negative `wrapcol`, then an alphabet that is not 85 bytes. -/
def B2a85OptionLaw : Prop :=
  (∀ (d : List Nat) (pad : Bool) (w : Nat) (alpha : Option (List Nat)),
    w < 2 ^ 64 → (∀ a, alpha = some a → a.length = 85) →
    b2aB85 (.bytes d) pad w (alpha.map .bytes) =
      (b2aB85 (.bytes (d ++ zeros85 d pad)) false 0 none).map (fun s0 =>
        let s := s0.map (tr85 (alpha.getD b85Alpha))
        if w ≠ 0 ∧ !s.isEmpty then wraplinesC s (if w < 5 then 5 else w / 5 * 5) else s)) ∧
  (∀ (d : List Nat) (pad : Bool) (w : Int) (alpha : Option Data), w < 0 →
    b2aB85 (.bytes d) pad w alpha = .error (.valueError "Cannot convert negative int")) ∧
  (∀ (d : List Nat) (pad : Bool) (w : Nat) (a : List Nat), w < 2 ^ 64 → a.length ≠ 85 →
    b2aB85 (.bytes d) pad w (some (.bytes a)) = .error (.valueError "alphabet must have length 85"))

theorem b2a85OptionLaw_proven : B2a85OptionLaw := by
  refine ⟨?_, ?_, ?_⟩
  · intro d pad w alpha hw ha
    have hs : sizeT (w : Int) = .ok w := by
      simp only [sizeT]
      rw [if_neg (by omega), if_neg (by omega)]
      rfl
    obtain ⟨A, hA, hAeq⟩ : ∃ A, encTable alpha b85Alpha 85 = .ok A ∧ alpha.getD b85Alpha = A := by
      cases alpha with
      | none => exact ⟨b85Alpha, rfl, rfl⟩
      | some a => exact ⟨a, by simp [encTable, ha a rfl], rfl⟩
    have hb : bufOpt (alpha.map .bytes) = .ok alpha := by cases alpha <;> rfl
    have hz : sizeT (0 : Int) = .ok 0 := rfl
    simp only [b2aB85, bufData, hs, hb, hA, hz, show bufOpt (none : Option Data) = .ok none from rfl,
      show encTable none b85Alpha 85 = .ok b85Alpha from rfl, bind, Except.bind, pure, Except.pure, Except.map]
    rw [hAeq]
    have e1 : b2aB85Core b85Alpha (d ++ zeros85 d pad) false 0 = enc85P b85Alpha d.length d pad := by
      have : b2aB85Core b85Alpha (d ++ zeros85 d pad) false 0 =
          enc85P b85Alpha (d ++ zeros85 d pad).length (d ++ zeros85 d pad) false := by
        simp only [b2aB85Core, enc85P]
        simp
      rw [this]
      cases pad with
      | false => simp [zeros85]
      | true =>
        rw [enc85P_padded b85Alpha d.length d (Nat.le_refl _)]
        apply enc85P_fuel b85Alpha false _ _ _ _ (Nat.le_refl _) (by omega)
        simp only [List.length_append, zeros85, if_true, List.length_replicate]
        omega
    rw [e1, ← enc85P_tr A pad]
    simp only [b2aB85Core, enc85P]
    first | rfl | simp
  · intro d pad w alpha hw
    simp [b2aB85, bufData, sizeT, hw, bind, Except.bind]
  · intro d pad w a hw ha
    have hs : sizeT (w : Int) = .ok w := by
      simp only [sizeT]
      rw [if_neg (by omega), if_neg (by omega)]
      rfl
    simp only [b2aB85, bufData, hs, bufOpt, encTable, bind, Except.bind, pure, Except.pure]
    rw [if_pos ha]
    rfl

end PyLean.TextLibs.Binascii
