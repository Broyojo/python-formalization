import PyLean.TextLibs.BinasciiB85b

/-!
The statements about `binascii.a2b_base85` and `binascii.b2a_base85`.
-/

namespace PyLean.TextLibs.Binascii

open PyLean

set_option linter.unusedSimpArgs false

/-- The bytes of the alphabet the base85 decoder reads. -/
def alphaChars85 : AlphaArg → List Nat
  | .absent => b85Alpha
  | .bytes a => a
  | .other _ => []

theorem b85_10 : (10 : Nat) ∉ b85Alpha := by decide +kernel

theorem a2bB85_eq (alpha : AlphaArg) (hA : (alphaChars85 alpha).length = 85) (s g : List Nat) (k : Bool) :
    a2bB85 (.bytes s) alpha (.bytes g) k =
      (a2bB85Loop (revT (alphaChars85 alpha) none) (if g.isEmpty then none else some g) k s.length (s.length + 6) s
        s.length {}).map (·.out) := by
  cases alpha with
  | absent =>
    simp only [a2bB85, asciiBuffer, alphaDec, bufData, decTable, alphaChars85, bind, Except.bind, pure, Except.pure]
    cases a2bB85Loop _ _ _ _ _ _ _ _ <;> rfl
  | bytes a =>
    simp only [alphaChars85] at hA
    simp only [a2bB85, asciiBuffer, alphaDec, bufData, decTable, alphaChars85, hA, ne_eq, not_true_eq_false,
      if_false, bind, Except.bind, pure, Except.pure]
    cases a2bB85Loop _ _ _ _ _ _ _ _ <;> rfl
  | other t => simp [alphaChars85] at hA

theorem toOption_ok {α : Type} (x : Py α) (v : α) (h : x.toOption = some v) : x = .ok v := by
  cases x with
  | error e => cases h
  | ok w => cases h; rfl

theorem digits85_mem (a : List Nat) (ha : a.length = 85) (w : Nat) : ∀ x ∈ digits85 a w, x ∈ a := by
  intro x hx
  simp only [digits85, List.mem_map, List.mem_range] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact getD_mem a _ (by rw [ha]; exact Nat.mod_lt _ (by decide))

theorem enc85P_mem (a : List Nat) (ha : a.length = 85) (pad : Bool) : ∀ (fe : Nat) (d : List Nat),
    ∀ x ∈ enc85P a fe d pad, x ∈ a := by
  intro fe
  induction fe with
  | zero =>
    intro d x hx
    unfold enc85P at hx
    rw [show fullB85 a 0 d = ([], d) from rfl, List.nil_append] at hx
    split at hx
    · simp at hx
    · exact digits85_mem a ha _ x (List.mem_of_mem_take hx)
  | succ fe ih =>
    intro d x hx
    by_cases hl : d.length ≥ 4
    · obtain ⟨p, q, r, e, t, rfl⟩ : ∃ p q r e t, d = p :: q :: r :: e :: t := by
        match d, hl with
        | p :: q :: r :: e :: t, _ => exact ⟨p, q, r, e, t, rfl⟩
      rw [enc85P_4] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact digits85_mem a ha _ x hx
      · exact ih t x hx
    · rw [enc85P_short a d (fe + 1) pad (by omega) (by intro e; subst e; simp [enc85P_nil] at hx)] at hx
      exact digits85_mem a ha _ x (List.mem_of_mem_take hx)

/-- `a2b_base85(b2a_base85(d, pad=p, wrapcol=w, alphabet=a), alphabet=a, ignorechars=g, canonical=k)` is
`d`, followed by the zero bytes `pad=True` added, for every `bytes` value `d` and every value of every
option, as long as the alphabet is 85 distinct bytes (without `'\n'` when the output is wrapped) and,
when it is wrapped, `ignorechars` names `'\n'`. -/
def B85RoundTripAll : Prop :=
  ∀ (d : List Nat) (alpha : Option (List Nat)) (pad : Bool) (w : Int) (g : List Nat) (k : Bool) (out : List Nat),
    (∀ x ∈ d, x < 256) →
    (∀ a, alpha = some a → a.length = 85 ∧ a.Nodup ∧ (w ≠ 0 → 10 ∉ a)) →
    (w ≠ 0 → 10 ∈ g) →
    b2aB85 (.bytes d) pad w (alpha.map .bytes) = .ok out →
    a2bB85 (.bytes out) (decAlphaOf alpha) (.bytes g) k = .ok (d ++ zeros85 d pad)

theorem b85RoundTripAll_proven : B85RoundTripAll := by
  intro d alpha pad w g k out hd ha hg h
  obtain ⟨n, hsz⟩ : ∃ n, sizeT w = .ok n := by
    cases hs : sizeT w with
    | ok n => exact ⟨n, rfl⟩
    | error e =>
      simp only [b2aB85, bufData, hs, bind, Except.bind] at h
      cases h
  have hn : w = (n : Int) := sizeT_ok w n hsz
  let alpha' := decAlphaOf alpha
  have hA : (alphaChars85 alpha').length = 85 ∧ (alphaChars85 alpha').Nodup ∧ (w ≠ 0 → 10 ∉ alphaChars85 alpha') := by
    cases alpha with
    | none => exact ⟨by decide, by decide +kernel, fun _ => b85_10⟩
    | some a => exact ha a rfl
  have hout : out = b2aB85Core (alphaChars85 alpha') d pad n := by
    cases alpha with
    | none =>
      simp only [b2aB85, bufData, bufOpt, encTable, Option.map, bind, Except.bind, pure, Except.pure, hsz] at h
      cases h; rfl
    | some a =>
      simp only [b2aB85, bufData, bufOpt, encTable, Option.map, bind, Except.bind, pure, Except.pure, hsz,
        (ha a rfl).1, ne_eq, not_true_eq_false, if_false] at h
      cases h; rfl
  subst hout
  obtain ⟨hAl, hAn, hA10⟩ := hA
  rw [a2bB85_eq alpha' hAl]
  generalize hAc : alphaChars85 alpha' = A at hAl hAn hA10
  generalize hig : (if g.isEmpty then none else some g) = ig
  let t := revT A none
  have ht : ∀ v, v < 85 → t (A.getD v 0) = v := fun v hv => revT_index A none v hAn (by omega) (by simp)
  let U := enc85P A d.length d pad
  have hU : ∀ x ∈ U, keep85 t ig x = true := by
    intro x hx
    have hm := enc85P_mem A hAl pad d.length d x hx
    have := revT_mem_any A none x hm (by simp)
    simp [keep85, t, Nat.not_le.mpr (by omega : revT A none x < 85)]
  have hN : n ≠ 0 → keep85 t ig 10 = false := by
    intro hw
    have hw' : w ≠ 0 := by omega
    have h10 : t 10 = 255 := revT_large A none 10 (by simp) (fun x hx e => hA10 hw' (e ▸ hx))
    have hg10 := hg hw'
    have hne : g ≠ [] := List.ne_nil_of_mem hg10
    rw [← hig]
    simp [keep85, h10, ign, hne, hg10]
  have hfilt : (b2aB85Core A d pad n).filter (keep85 t ig) = U := by
    have e : b2aB85Core A d pad n =
        if n ≠ 0 ∧ !U.isEmpty then wraplinesC U (if n < 5 then 5 else n / 5 * 5) else U := by
      simp only [b2aB85Core, U, enc85P]
    rw [e]
    split
    · rename_i hc
      have hpos : 0 < (if n < 5 then 5 else n / 5 * 5) := by split <;> omega
      exact wraplinesC_filterP _ hpos _ (hN hc.1) _ _ (Nat.le_refl _) hU
    · exact List.filter_eq_self.mpr hU
  have hf := b85_filter t ig k (b2aB85Core A d pad n).length U.length (b2aB85Core A d pad n) {} _ (U.length + 6)
    (by decide) (Nat.le_refl _) (by simp [hfilt])
  rw [hfilt] at hf
  have hdec := dec85G_main A t ht k U.length pad d.length d (Nat.le_refl _) hd d.length (U.length + 6) []
    (Nat.le_refl _) (Nat.le_refl _)
  have e0 : ({} : St85) = ⟨0, 0, []⟩ := rfl
  rw [e0] at hf
  rw [hdec] at hf
  rw [e0, toOption_ok _ _ hf]
  simp [Except.map]

end PyLean.TextLibs.Binascii
