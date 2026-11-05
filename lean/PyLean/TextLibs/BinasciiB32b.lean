import PyLean.TextLibs.BinasciiB32

/-!
The statements about `binascii.a2b_base32` and `binascii.b2a_base32` over every option.
-/

namespace PyLean.TextLibs.Binascii

open PyLean

set_option linter.unusedSimpArgs false

/-- The bytes of the alphabet the base32 decoder reads. -/
def alphaChars32 : AlphaArg → List Nat
  | .absent => b32Alpha
  | .bytes a => a
  | .other _ => []

/-- The table the base32 decoder reads: the static one, or the one `get_reverse_table` builds. -/
def tbl32 : AlphaArg → Nat → Nat
  | .absent => revT b32Alpha none
  | .bytes a => revT a (some 61)
  | .other _ => fun _ => 255

theorem b32_61 : (61 : Nat) ∉ b32Alpha := by decide +kernel

/-- The arguments either fail whatever the data, or leave the loop with the table of a 32-byte
alphabet. -/
theorem a2bB32_cases (alpha : AlphaArg) :
    (∃ e, ∀ s p g k, a2bB32 (.bytes s) p alpha (.bytes g) k = .error e) ∨
    ((alphaChars32 alpha).length = 32 ∧ ∀ s p g k, a2bB32 (.bytes s) p alpha (.bytes g) k =
      a2b32Core (tbl32 alpha) p (if g.isEmpty then none else some g) k s) := by
  cases alpha with
  | absent =>
    right
    refine ⟨by decide, fun s p g k => ?_⟩
    simp [a2bB32, asciiBuffer, alphaDec, bufData, decTable, tbl32, bind, Except.bind]
  | bytes a =>
    by_cases hl : a.length = 32
    · right
      refine ⟨hl, fun s p g k => ?_⟩
      simp [a2bB32, asciiBuffer, alphaDec, bufData, decTable, hl, tbl32, alphaChars32, bind, Except.bind]
    · left
      refine ⟨.valueError s!"alphabet must have length {32}", fun s p g k => ?_⟩
      simp [a2bB32, asciiBuffer, alphaDec, bufData, decTable, hl, bind, Except.bind]
  | other t =>
    left
    refine ⟨.typeError s!"{"a2b_base32"}() argument 'alphabet' must be bytes, not {t}", fun s p g k => ?_⟩
    simp [a2bB32, asciiBuffer, alphaDec, bind, Except.bind]

theorem a2bB32_eq (alpha : AlphaArg) (hA : (alphaChars32 alpha).length = 32) :
    ∀ s p g k, a2bB32 (.bytes s) p alpha (.bytes g) k =
      a2b32Core (tbl32 alpha) p (if g.isEmpty then none else some g) k s := by
  intro s p g k
  cases alpha with
  | absent => simp [a2bB32, asciiBuffer, alphaDec, bufData, decTable, tbl32, bind, Except.bind]
  | bytes a =>
    simp only [alphaChars32] at hA
    simp [a2bB32, asciiBuffer, alphaDec, bufData, decTable, hA, tbl32, bind, Except.bind]
  | other t => simp [alphaChars32] at hA

theorem tbl32_lt (alpha : AlphaArg) (hA : (alphaChars32 alpha).length = 32) (x : Nat) :
    tbl32 alpha x < 32 ↔ (x ∈ alphaChars32 alpha ∧ x ≠ 61) := by
  cases alpha with
  | absent =>
    simp only [tbl32, alphaChars32]
    constructor
    · intro h
      have hm : x ∈ b32Alpha := by
        by_cases hx : x ∈ b32Alpha
        · exact hx
        · rw [revT_large b32Alpha none x (by simp) (fun y hy e => hx (e ▸ hy))] at h
          omega
      exact ⟨hm, fun e => b32_61 (e ▸ hm)⟩
    · intro ⟨hx, _⟩
      have := revT_mem_any b32Alpha none x hx (by simp)
      have e : b32Alpha.length = 32 := by decide
      omega
  | bytes a =>
    simp only [tbl32, alphaChars32] at hA ⊢
    constructor
    · intro h
      by_cases h61 : x = 61
      · subst h61
        rw [revT_pad, hA] at h
        omega
      · refine ⟨?_, h61⟩
        by_cases hx : x ∈ a
        · exact hx
        · rw [revT_large a (some 61) x (by simpa using Ne.symm h61) (fun y hy e => hx (e ▸ hy))] at h
          omega
    · intro ⟨hx, h61⟩
      have := revT_mem_any a (some 61) x hx (by simpa using Ne.symm h61)
      omega
  | other t => simp [alphaChars32] at hA

theorem tbl32_61 (alpha : AlphaArg) (hA : (alphaChars32 alpha).length = 32) : 32 ≤ tbl32 alpha 61 := by
  have := mt (tbl32_lt alpha hA 61).mp (by simp)
  omega

/-! ### The round trip -/

theorem fastEnc32_mem (a : List Nat) (ha : a.length = 32) : ∀ (f : Nat) (d : List Nat),
    ∀ x ∈ (fastEnc32 a f d).1, x ∈ a := by
  intro f
  induction f with
  | zero => intro d x hx; simp [fastEnc32] at hx
  | succ f ih =>
    intro d x hx
    simp only [fastEnc32] at hx
    split at hx
    · simp only [List.mem_append, List.mem_map, List.mem_range] at hx
      rcases hx with ⟨i, _, rfl⟩ | hx
      · exact getD_mem a _ (by rw [ha]; exact Nat.mod_lt _ (by decide))
      · exact ih _ x hx
    · simp at hx

theorem tail32_mem (a : List Nat) (ha : a.length = 32) (r : List Nat) : ∀ x ∈ tail32 a r, x ∈ a := by
  intro x hx
  have hg : ∀ v, a.getD (v % 32) 0 ∈ a := fun v => getD_mem a _ (by rw [ha]; exact Nat.mod_lt _ (by decide))
  match r with
  | [] => simp [tail32] at hx
  | [_] =>
    simp only [tail32, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> exact hg _
  | [_, _] =>
    simp only [tail32, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact hg _
  | [_, _, _] =>
    simp only [tail32, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact hg _
  | [_, _, _, _] =>
    simp only [tail32, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hg _
  | _ :: _ :: _ :: _ :: _ :: _ => simp [tail32] at hx

theorem inv32_of (alpha : AlphaArg) (hA : (alphaChars32 alpha).length = 32) (hn : (alphaChars32 alpha).Nodup)
    (h61 : 61 ∉ alphaChars32 alpha) : Inv32 (alphaChars32 alpha) (tbl32 alpha) := by
  refine ⟨fun v hv => ?_, tbl32_61 alpha hA⟩
  have hm : (alphaChars32 alpha).getD v 0 ∈ alphaChars32 alpha := getD_mem _ v (by omega)
  have hne : (alphaChars32 alpha).getD v 0 ≠ 61 := fun e => h61 (e ▸ hm)
  cases alpha with
  | absent => exact revT_index b32Alpha none v hn (by simp only [alphaChars32] at hA; omega) (by simp)
  | bytes a =>
    exact revT_index a (some 61) v hn (by simp only [alphaChars32] at hA; omega)
      (fun e => hne (Option.some.inj e).symm)
  | other t => simp [alphaChars32] at hA

/-- `a2b_base32(b2a_base32(d, padded=p, wrapcol=w, alphabet=a), padded=p, alphabet=a, ignorechars=g,
canonical=k) == d`, for every `bytes` value `d` and every value of every option, as long as the alphabet
is 32 distinct bytes without `'='` (and without `'\n'` when the output is wrapped) and, when it is
wrapped, `ignorechars` names `'\n'`. -/
def B32RoundTripAll : Prop :=
  ∀ (d : List Nat) (alpha : Option (List Nat)) (p : Bool) (w : Int) (g : List Nat) (k : Bool) (out : List Nat),
    (∀ x ∈ d, x < 256) →
    (∀ a, alpha = some a → a.length = 32 ∧ a.Nodup ∧ 61 ∉ a ∧ (w ≠ 0 → 10 ∉ a)) →
    (w ≠ 0 → 10 ∈ g) →
    b2aB32 (.bytes d) p w (alpha.map .bytes) = .ok out →
    a2bB32 (.bytes out) p (decAlphaOf alpha) (.bytes g) k = .ok d

theorem b32RoundTripAll_proven : B32RoundTripAll := by
  intro d alpha p w g k out hd ha hg h
  obtain ⟨n, hsz⟩ : ∃ n, sizeT w = .ok n := by
    cases hs : sizeT w with
    | ok n => exact ⟨n, rfl⟩
    | error e =>
      simp only [b2aB32, bufData, hs, bind, Except.bind] at h
      cases h
  have hn : w = (n : Int) := sizeT_ok w n hsz
  let alpha' := decAlphaOf alpha
  have hA : (alphaChars32 alpha').length = 32 ∧ (alphaChars32 alpha').Nodup ∧ 61 ∉ alphaChars32 alpha' ∧
      (w ≠ 0 → 10 ∉ alphaChars32 alpha') := by
    cases alpha with
    | none => exact ⟨by decide, by decide +kernel, b32_61, fun _ => by decide +kernel⟩
    | some a => exact ha a rfl
  have hout : out = b2a32Core (alphaChars32 alpha') d p n := by
    cases alpha with
    | none =>
      simp only [b2aB32, bufData, bufOpt, encTable, Option.map, bind, Except.bind, pure, Except.pure, hsz] at h
      cases h; rfl
    | some a =>
      simp only [b2aB32, bufData, bufOpt, encTable, Option.map, bind, Except.bind, pure, Except.pure, hsz,
        (ha a rfl).1, ne_eq, not_true_eq_false, if_false] at h
      cases h; rfl
  subst hout
  obtain ⟨hAl, hAn, hA61, hA10⟩ := hA
  generalize hAc : alphaChars32 alpha' = A at hAl hAn hA61 hA10
  have hinv : Inv32 A (tbl32 alpha') := hAc ▸ inv32_of alpha' (hAc ▸ hAl) (hAc ▸ hAn) (hAc ▸ hA61)
  have hlt : ∀ x, tbl32 alpha' x < 32 ↔ (x ∈ A ∧ x ≠ 61) := fun x => hAc ▸ tbl32_lt alpha' (hAc ▸ hAl) x
  rw [a2bB32_eq alpha' (hAc ▸ hAl), core32_slow _ _ _ hinv.h61, slow32_filter]
  generalize hig : (if g.isEmpty then none else some g) = ig
  let U := enc32B A d.length d ++ List.replicate (if p then pads32 d.length else 0) 61
  have hU : ∀ x ∈ U, (!skip32 (tbl32 alpha') p ig x) = true := by
    intro x hx
    simp only [U, List.mem_append] at hx
    rcases hx with hx | hx
    · have hm : x ∈ A := by
        simp only [enc32B, List.mem_append] at hx
        rcases hx with hx | hx
        · exact fastEnc32_mem A hAl _ _ x hx
        · exact tail32_mem A hAl _ x hx
      have := (hlt x).mpr ⟨hm, fun e => hA61 (e ▸ hm)⟩
      simp [skip32, Nat.not_le.mpr this]
    · cases p with
      | false => simp at hx
      | true =>
        have := List.eq_of_mem_replicate hx
        subst this
        simp [skip32]
  have hN : n ≠ 0 → (!skip32 (tbl32 alpha') p ig 10) = false := by
    intro hw
    have hw' : w ≠ 0 := by omega
    have h10 : ¬ tbl32 alpha' 10 < 32 := fun h' => hA10 hw' ((hlt 10).mp h').1
    have hg10 := hg hw'
    have hne : g ≠ [] := List.ne_nil_of_mem hg10
    rw [← hig]
    simp [skip32, Nat.not_lt.mp h10, ign, hne, hg10]
  have hfilt : (b2a32Core A d p n).filter (fun x => !skip32 (tbl32 alpha') p ig x) = U := by
    have e : b2a32Core A d p n =
        if n ≠ 0 ∧ !U.isEmpty then wraplinesC U (if n < 8 then 8 else n / 8 * 8) else U := by
      simp only [b2a32Core, U, enc32B, pads32]
      rfl
    rw [e]
    split
    · rename_i hc
      have hpos : 0 < (if n < 8 then 8 else n / 8 * 8) := by split <;> omega
      exact wraplinesC_filterP _ hpos _ (hN hc.1) _ _ (Nat.le_refl _) hU
    · exact List.filter_eq_self.mpr hU
  rw [hfilt]
  obtain ⟨st, h1, h2⟩ := dec_enc32 A (tbl32 alpha') hinv p ig k d.length d (Nat.le_refl _) hd d.length []
    (Nat.le_refl _)
  have e0 : ({} : Dec32) = ⟨0, 0, 0, []⟩ := rfl
  rw [e0, h1]
  exact h2

end PyLean.TextLibs.Binascii
