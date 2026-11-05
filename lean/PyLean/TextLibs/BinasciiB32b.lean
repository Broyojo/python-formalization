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

/-! ### What the decoder rejects -/

/-- A run that cannot end well: it raises, or it stops at a pad after 1, 3 or 6 data characters of a
group (the `break` of `Modules/binascii.c:1736-1739`), which the check after the loop refuses. -/
def Doomed32 (t : Nat → Nat) (p : Bool) (ig : Option (List Nat)) (s : List Nat) (st : Dec32) : Prop :=
  ∀ st', slow32 t p ig s st = .ok st' → (st'.octa == 1 || st'.octa == 3 || st'.octa == 6) = true

theorem doomed32_prefix (t : Nat → Nat) (p : Bool) (ig : Option (List Nat)) (m : List Nat)
    (hm : ∀ st, Doomed32 t p ig m st) : ∀ (s1 : List Nat) (st : Dec32), Doomed32 t p ig (s1 ++ m) st := by
  intro s1
  induction s1 with
  | nil => intro st; simpa using hm st
  | cons x xs ih =>
    intro st st' h
    simp only [List.cons_append, slow32] at h
    split at h
    · split at h
      · exact ih _ _ h
      · split at h
        · exact ih _ _ h
        · split at h
          · rename_i hq
            injection h with h
            subst h
            exact hq
          · cases h
    · split at h
      · split at h
        · cases h
        · exact ih _ _ h
      · split at h
        · cases h
        · split at h
          · exact ih _ _ h
          · exact ih _ _ h

theorem doomed32_core (t : Nat → Nat) (p : Bool) (ig : Option (List Nat)) (h61 : 32 ≤ t 61) (k : Bool) (s : List Nat)
    (h : Doomed32 t p ig s {}) : ∀ r, a2b32Core t p ig k s ≠ .ok r := by
  intro r hr
  rw [core32_slow t p ig h61] at hr
  cases hs : slow32 t p ig s {} with
  | error e => rw [hs] at hr; cases hr
  | ok st =>
    rw [hs] at hr
    have hq := h st hs
    simp [Except.bind, fin32, hq, bind, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at hr

theorem doomed32_junk (t : Nat → Nat) (p : Bool) (ig : Option (List Nat)) (x : Nat) (hx : 32 ≤ t x)
    (hp : ¬(p = true ∧ x = 61)) (hi : ign ig x = false) (r : List Nat) (st : Dec32) : Doomed32 t p ig (x :: r) st := by
  intro st' h
  have h1 : (p && x == 61) = false := by
    cases p <;> simp_all
  simp [slow32, h1, hx, hi] at h

theorem doomed32_pads (t : Nat → Nat) (ig : Option (List Nat)) (hi : ign ig 61 = false) (h61 : 32 ≤ t 61)
    (y : Nat) (hy : t y < 32) (r : List Nat) :
    ∀ (s2 : List Nat) (st : Dec32), 0 < st.pads → Doomed32 t true ig (s2 ++ y :: r) st := by
  have hy61 : (y == 61) = false := by
    apply beq_false_of_ne; intro e; subst e; omega
  intro s2
  induction s2 with
  | nil =>
    intro st hpos st' h
    simp only [List.nil_append, slow32, hy61, Bool.and_false, Bool.false_eq_true, if_false,
      if_neg (Nat.not_le.mpr hy), hi] at h
    rw [if_pos (by simp; omega)] at h
    cases h
  | cons x xs ih =>
    intro st hpos st' h
    simp only [List.cons_append, slow32] at h
    split at h
    · split at h
      · exact ih _ (by simp) _ h
      · split at h
        · exact ih _ (by simp) _ h
        · split at h
          · rename_i hq
            injection h with h
            subst h
            exact hq
          · cases h
    · split at h
      · split at h
        · cases h
        · exact ih _ hpos _ h
      · rw [if_pos (by simp [hi]; omega)] at h
        cases h

theorem doomed32_eq (t : Nat → Nat) (ig : Option (List Nat)) (hi : ign ig 61 = false) (h61 : 32 ≤ t 61)
    (y : Nat) (hy : t y < 32) (s2 r : List Nat) (st : Dec32) : Doomed32 t true ig (61 :: s2 ++ y :: r) st := by
  intro st' h
  simp only [List.cons_append, slow32, beq_self_eq_true, Bool.and_self, if_true, hi, Bool.false_eq_true,
    if_false] at h
  split at h
  · exact doomed32_pads t ig hi h61 y hy r s2 _ (by simp) _ h
  · split at h
    · rename_i _ hq
      injection h with h
      subst h
      exact hq
    · cases h

/-- What `a2b_base32` refuses, for every option: a byte that is not in the alphabet (or a `'='` when
`padded=False`) that `ignorechars` does not name, and, with `padded=True` and no `'='` in `ignorechars`,
any data character after a `'='`. A decoder that skips unknown bytes, or reads on after the padding,
does not satisfy this; `B32RoundTripAll` rules out one that always raises. -/
def B32StrictLaw : Prop :=
  ∀ (s : List Nat) (p : Bool) (alpha : AlphaArg) (g : List Nat) (k : Bool),
    ((∃ x ∈ s, (x ≠ 61 → x ∉ alphaChars32 alpha) ∧ (x = 61 → p = false) ∧ x ∉ g) →
      ∀ r, a2bB32 (.bytes s) p alpha (.bytes g) k ≠ .ok r) ∧
    (p = true → 61 ∉ g → ∀ s1 s2 y s3, s = s1 ++ 61 :: s2 ++ y :: s3 →
      y ∈ alphaChars32 alpha → y ≠ 61 → ∀ r, a2bB32 (.bytes s) p alpha (.bytes g) k ≠ .ok r)

theorem ign_g (g : List Nat) (x : Nat) (h : x ∉ g) : ign (if g.isEmpty then none else some g) x = false := by
  cases g with
  | nil => rfl
  | cons a l => simpa [ign] using h

theorem b32StrictLaw_proven : B32StrictLaw := by
  intro s p alpha g k
  rcases a2bB32_cases alpha with ⟨e, he⟩ | ⟨hA, he⟩
  · refine ⟨fun _ r h => ?_, fun _ _ _ _ _ _ _ _ _ r h => ?_⟩
    · rw [he] at h; cases h
    · rw [he] at h; cases h
  · have h61 := tbl32_61 alpha hA
    constructor
    · rintro ⟨x, hx, h1, h2, h3⟩ r hr
      rw [he] at hr
      obtain ⟨s1, s3, rfl⟩ := List.append_of_mem hx
      have hjunk : ∀ st, Doomed32 (tbl32 alpha) p (if g.isEmpty then none else some g) (x :: s3) st := by
        intro st
        apply doomed32_junk _ p _ x
        · by_cases hx61 : x = 61
          · subst hx61; exact h61
          · have := mt (tbl32_lt alpha hA x).mp (by simp [h1 hx61])
            omega
        · intro ⟨hp, hx61⟩
          have := h2 hx61
          simp_all
        · exact ign_g g x h3
      exact doomed32_core _ p _ h61 k _ (doomed32_prefix _ _ _ _ hjunk s1 {}) r hr
    · intro hp hg s1 s2 y s3 hseq hy hy61 r hr
      subst hp
      rw [he, hseq] at hr
      have hyt : tbl32 alpha y < 32 := (tbl32_lt alpha hA y).mpr ⟨hy, hy61⟩
      have hm : ∀ st, Doomed32 (tbl32 alpha) true _ (61 :: s2 ++ y :: s3) st :=
        fun st => doomed32_eq _ _ (ign_g g 61 hg) h61 y hyt s2 s3 st
      have := doomed32_prefix _ _ _ _ hm s1 {}
      simp only [List.cons_append] at this hr
      exact doomed32_core _ true _ h61 k _ (by simpa using this) r hr

/-! ### `canonical` -/

/-- The bits after the last whole byte, for the values of the data characters in order; the decoder
refuses 1, 3 or 6 characters over a group before it looks at them. -/
def resid32 (vs : List Nat) : Nat :=
  match vs.length % 8 with
  | 2 => vs.getLast?.getD 0 % 4
  | 4 => vs.getLast?.getD 0 % 16
  | 5 => vs.getLast?.getD 0 % 2
  | 7 => vs.getLast?.getD 0 % 8
  | _ => 0

def Res32 (st : Dec32) (vs : List Nat) : Prop :=
  st.octa = vs.length % 8 ∧ ((st.octa == 1 || st.octa == 3 || st.octa == 6) = false → st.left = resid32 vs)

theorem dec32_inv (st : Dec32) (vs : List Nat) (v : Nat) (h : Res32 st vs) : Res32 (decStep32 st v) (vs ++ [v]) := by
  obtain ⟨h1, _⟩ := h
  have hl : (vs ++ [v]).length % 8 = (vs.length % 8 + 1) % 8 := by
    simp only [List.length_append, List.length_singleton]; omega
  have hlast : (vs ++ [v]).getLast?.getD 0 = v := by simp
  obtain ⟨q, p, l, o⟩ := st
  simp only at h1
  unfold Res32 resid32
  rw [hl, hlast]
  rcases (by omega : vs.length % 8 = 0 ∨ vs.length % 8 = 1 ∨ vs.length % 8 = 2 ∨ vs.length % 8 = 3 ∨
      vs.length % 8 = 4 ∨ vs.length % 8 = 5 ∨ vs.length % 8 = 6 ∨ vs.length % 8 = 7) with
    h | h | h | h | h | h | h | h
  all_goals (rw [h] at h1; subst h1; simp [decStep32, h])

theorem res32_pads (st : Dec32) (vs : List Nat) (n : Nat) (h : Res32 st vs) : Res32 { st with pads := n } vs := h

theorem slow32_resid (t : Nat → Nat) (p : Bool) (ig : Option (List Nat)) (h61 : 32 ≤ t 61) :
    ∀ (s : List Nat) (st st1 : Dec32) (vs : List Nat), slow32 t p ig s st = .ok st1 →
      (st1.octa == 1 || st1.octa == 3 || st1.octa == 6) = false → Res32 st vs →
      Res32 st1 (vs ++ (s.filter (fun x => decide (t x < 32))).map t) := by
  intro s
  induction s with
  | nil => intro st st1 vs h _ hi; cases h; simpa using hi
  | cons x xs ih =>
    intro st st1 vs h hq hi
    simp only [slow32] at h
    split at h
    · rename_i hpx
      have hx : x = 61 := by simp at hpx; exact hpx.2
      subst hx
      rw [List.filter_cons_of_neg (by simp; omega)]
      split at h
      · exact ih _ _ _ h hq (res32_pads _ _ _ hi)
      · split at h
        · exact ih _ _ _ h hq (res32_pads _ _ _ hi)
        · split at h
          · rename_i hq1
            injection h with h
            subst h
            simp only at hq
            rw [hq1] at hq
            cases hq
          · cases h
    · split at h
      · rename_i hv
        rw [List.filter_cons_of_neg (by simp; omega)]
        split at h
        · cases h
        · exact ih _ _ _ h hq hi
      · rename_i hv
        rw [List.filter_cons_of_pos (by simp; omega)]
        split at h
        · cases h
        · split at h
          · have := ih _ _ _ h hq (res32_pads _ _ 0 (dec32_inv st vs (t x) hi))
            simpa using this
          · have := ih _ _ _ h hq (dec32_inv st vs (t x) hi)
            simpa using this

/-- `canonical=True` is `canonical=False` and one more check: a result whose last group leaves non-zero
bits after its last whole byte is refused with "Non-zero padding bits", for every other option. -/
def B32CanonicalLaw : Prop :=
  ∀ (s : List Nat) (p : Bool) (alpha : AlphaArg) (g : List Nat),
    a2bB32 (.bytes s) p alpha (.bytes g) true =
      (a2bB32 (.bytes s) p alpha (.bytes g) false).bind (fun r =>
        if resid32 ((s.filter (fun x => decide (x ∈ alphaChars32 alpha) && x != 61)).map (tbl32 alpha)) ≠ 0
        then .error (err "Non-zero padding bits") else .ok r)

theorem b32CanonicalLaw_proven : B32CanonicalLaw := by
  intro s p alpha g
  rcases a2bB32_cases alpha with ⟨e, he⟩ | ⟨hA, he⟩
  · rw [he, he]; rfl
  · rw [he, he]
    have h61 := tbl32_61 alpha hA
    rw [core32_slow _ _ _ h61, core32_slow _ _ _ h61]
    have hf : s.filter (fun x => decide (x ∈ alphaChars32 alpha) && x != 61) =
        s.filter (fun x => decide (tbl32 alpha x < 32)) := by
      apply List.filter_congr
      intro x _
      have := tbl32_lt alpha hA x
      by_cases h2 : x = 61
      · subst h2
        simp [Nat.not_lt.mpr h61]
      · by_cases h1 : x ∈ alphaChars32 alpha
        · simp [h1, h2, this.mpr ⟨h1, h2⟩]
        · have h3 : ¬ tbl32 alpha x < 32 := fun h' => h1 (this.mp h').1
          simp [h1, h3]
    rw [hf]
    cases hs : slow32 (tbl32 alpha) p (if g.isEmpty then none else some g) s {} with
    | error e => rfl
    | ok st =>
      simp only [Except.bind]
      by_cases hq : (st.octa == 1 || st.octa == 3 || st.octa == 6) = true
      · simp [fin32, hq, bind, Except.bind, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]
      · have hq' : (st.octa == 1 || st.octa == 3 || st.octa == 6) = false := by simpa using hq
        have hinv := slow32_resid _ _ _ h61 s {} st [] hs hq' ⟨rfl, fun _ => rfl⟩
        simp only [List.nil_append] at hinv
        rw [← hinv.2 hq']
        unfold fin32
        simp only [hq', Bool.false_eq_true, if_false]
        by_cases hpd : (p = true ∧ st.octa ≠ 0 ∧ st.octa + st.pads < 8)
        · simp [hpd, bind, Except.bind, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]
        · simp [hpd, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]

/-! ### `'='` in `ignorechars` -/

/-- The statement `B64PadBeforeDataIgnored` proves of `a2b_base64`: with `'='` in `ignorechars`, a `'='`
that a data character follows can be taken out without changing anything (the docs: "the pad
characters presented before the end of the encoded data ... will be ignored"). False: the decoder never
sets `pads` back to 0 after a data character (`Modules/binascii.c:1771-1781`, where `a2b_base64` has
`pads = 0;` at `:873`), so the ignored `'='` still counts as padding at the end.
`a2b_base32(b'AAAA=AAA', ignorechars=b'=')` returns 4 bytes, `a2b_base32(b'AAAAAAA', ignorechars=b'=')`
raises "Incorrect padding". -/
def B32PadBeforeDataIgnored : Prop :=
  ∀ (s1 s2 : List Nat) (y : Nat) (alpha : AlphaArg) (g : List Nat) (k : Bool),
    61 ∈ g → y ∈ alphaChars32 alpha → y ≠ 61 →
    a2bB32 (.bytes (s1 ++ 61 :: y :: s2)) true alpha (.bytes g) k =
      a2bB32 (.bytes (s1 ++ y :: s2)) true alpha (.bytes g) k

theorem b32PadBeforeDataIgnored_refuted : ¬B32PadBeforeDataIgnored := by
  intro h
  have := h [65, 65, 65, 65] [65, 65] 65 .absent [61] false (by decide) (by decide +kernel) (by decide)
  revert this
  decide +kernel

end PyLean.TextLibs.Binascii
