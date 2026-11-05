import PyLean.TextLibs.BinasciiB64

/-!
More of `binascii.a2b_base64` over every option: what the lenient mode discards, that the strict mode
only takes away, what `canonical` adds, and how a `'='` that is ignored before data behaves. Then the
encoder, `b2a_base64`, over every option.
-/

namespace PyLean.TextLibs.Binascii

open PyLean

set_option linter.unusedSimpArgs false

/-! ### Strict mode only takes away -/

theorem slow_strict_lenient (t : Nat → Nat) (p : Bool) (ig : Option (List Nat)) :
    ∀ (s : List Nat) (st st1 : Dec), slow64 ⟨true, p, t, ig⟩ s st = .ok st1 → st1.quad ≠ 1 →
      slow64 ⟨false, p, t, none⟩ s st = .ok st1 := by
  intro s
  induction s with
  | nil => intro st st1 h _; exact h
  | cons x xs ih =>
    intro st st1 h hq
    simp only [slow64] at h ⊢
    split at h
    · rename_i hpx
      simp only [hpx, if_true]
      split at h
      · rename_i hv
        rw [if_pos hv]
        exact ih _ _ h hq
      · rename_i hv
        rw [if_neg hv]
        split at h
        · exact ih _ _ h hq
        · split at h
          · rename_i hq1
            injection h with h
            subst h
            exact absurd hq1 hq
          · cases h
    · rename_i hpx
      simp only [hpx, Bool.false_eq_true, if_false]
      split at h
      · rename_i hv
        rw [if_pos hv]
        split at h
        · cases h
        · simp only [Bool.false_and, Bool.false_eq_true, if_false]
          exact ih _ _ h hq
      · rename_i hv
        rw [if_neg hv]
        split at h
        · cases h
        · simp only [Bool.false_eq_true, and_false, false_and, if_false]
          exact ih _ _ h hq

theorem fin64_quad (c : B64) (k : Bool) (st : Dec) (r : List Nat) (h : fin64 c k st = .ok r) : st.quad ≠ 1 := by
  intro hq
  simp [fin64, hq, bind, Except.bind, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at h

/-- Whatever `strict_mode=True` accepts, `strict_mode=False` accepts with the same result, for every
other option (`ignorechars` is then not used). -/
def B64StrictImpliesLenient : Prop :=
  ∀ (s r : List Nat) (p : Bool) (alpha : AlphaArg) (g : Option (List Nat)) (k : Bool),
    a2bB64 (.bytes s) (some true) p alpha (g.map .bytes) k = .ok r →
    a2bB64 (.bytes s) (some false) p alpha (g.map .bytes) k = .ok r

theorem b64StrictImpliesLenient_proven : B64StrictImpliesLenient := by
  intro s r p alpha g k h
  rcases a2bB64_cases alpha with ⟨e, he⟩ | ⟨hA, he⟩
  · rw [he] at h; cases h
  · rw [he] at h ⊢
    have h61 := tbl64_61 _ hA
    rw [core_slow _ h61] at h ⊢
    have hl : igEff (some false) g = none := by simp [igEff]
    simp only [Option.getD_some, hl] at h ⊢
    cases hs : slow64 ⟨true, p, revT (alphaChars alpha) (some 61), igEff (some true) g⟩ s {} with
    | error e => rw [hs] at h; cases h
    | ok st =>
      rw [hs] at h
      have hq := fin64_quad _ k st r h
      rw [slow_strict_lenient _ p _ s {} st hs hq]
      exact h

/-! ### What the lenient mode discards -/

/-- The bytes a non-strict decoding reads: the alphabet but `'='`, and `'='` when `padded`. -/
def keep64 (alpha : AlphaArg) (p : Bool) (x : Nat) : Bool :=
  (decide (x ∈ alphaChars alpha) && x != 61) || (p && x == 61)

/-- With `strict_mode=False`, taking out every byte that is not in the alphabet (or is `'='` with
`padded=False`) changes nothing, failures and their messages included, and `ignorechars` is not used:
"non-alphabet characters are discarded". -/
def B64LenientFilter : Prop :=
  ∀ (s : List Nat) (p : Bool) (alpha : AlphaArg) (g : Option (List Nat)) (k : Bool),
    a2bB64 (.bytes s) (some false) p alpha (g.map .bytes) k =
      a2bB64 (.bytes (s.filter (keep64 alpha p))) (some false) p alpha none k

theorem b64LenientFilter_proven : B64LenientFilter := by
  intro s p alpha g k
  rcases a2bB64_cases alpha with ⟨e, he⟩ | ⟨hA, he⟩
  · have h2 := he (s.filter (keep64 alpha p)) (some false) p none k
    simp only [Option.map_none] at h2
    rw [he, h2]
  · have h2 := he (s.filter (keep64 alpha p)) (some false) p none k
    simp only [Option.map_none] at h2
    rw [he, h2]
    have h61 := tbl64_61 _ hA
    have hl : igEff (some false) g = none := by simp [igEff]
    have hl2 : igEff (some false) none = none := by simp [igEff]
    simp only [Option.getD_some, hl, hl2]
    rw [core_slow _ h61, core_slow _ h61, slow_filter _ s]
    have : s.filter (fun x => !skip64 ⟨false, p, revT (alphaChars alpha) (some 61), none⟩ x) = s.filter (keep64 alpha p) := by
      apply List.filter_congr
      intro x _
      have := tbl64_lt _ hA x
      by_cases hx : x = 61
      · subst hx
        cases p <;> simp [skip64, keep64, h61]
      · by_cases hm : x ∈ alphaChars alpha
        · have hlt := this.mpr ⟨hm, hx⟩
          simp [skip64, keep64, hm, hx, Nat.not_le.mpr hlt]
        · have hge : ¬ revT (alphaChars alpha) (some 61) x < 64 := fun h => hm (this.mp h).1
          simp [skip64, keep64, hm, hx, Nat.not_lt.mp hge]
    rw [this]

/-! ### `canonical` -/

/-- The bits after the last whole byte, for the values of the data characters in order. -/
def resid64 (vs : List Nat) : Nat :=
  match vs.length % 4 with
  | 0 => 0
  | 1 => vs.getLast?.getD 0
  | 2 => vs.getLast?.getD 0 % 16
  | _ => vs.getLast?.getD 0 % 4

def ResidInv (st : Dec) (vs : List Nat) : Prop := st.quad = vs.length % 4 ∧ st.left = resid64 vs

theorem decStep_inv (st : Dec) (vs : List Nat) (v : Nat) (h : ResidInv st vs) :
    ResidInv (decStep { st with pads := 0 } v) (vs ++ [v]) := by
  obtain ⟨h1, h2⟩ := h
  have hlt : vs.length % 4 < 4 := Nat.mod_lt _ (by decide)
  have hl : (vs ++ [v]).length % 4 = (vs.length % 4 + 1) % 4 := by
    simp only [List.length_append, List.length_singleton]; omega
  have hlast : (vs ++ [v]).getLast?.getD 0 = v := by simp
  obtain ⟨q, p, l, o⟩ := st
  simp only at h1 h2
  unfold ResidInv resid64
  rw [hl, hlast]
  rcases (by omega : vs.length % 4 = 0 ∨ vs.length % 4 = 1 ∨ vs.length % 4 = 2 ∨ vs.length % 4 = 3)
    with h | h | h | h
  all_goals (rw [h] at h1; subst h1; simp [decStep, h])

theorem slow_resid (c : B64) (h61 : 64 ≤ c.tbl 61) : ∀ (s : List Nat) (st st1 : Dec) (vs : List Nat),
    slow64 c s st = .ok st1 → st1.quad ≠ 1 → ResidInv st vs →
      ResidInv st1 (vs ++ (s.filter (fun x => decide (c.tbl x < 64))).map c.tbl) := by
  intro s
  induction s with
  | nil => intro st st1 vs h _ hi; cases h; simpa using hi
  | cons x xs ih =>
    intro st st1 vs h hq hi
    simp only [slow64] at h
    split at h
    · rename_i hpx
      have hx : x = 61 := by simp at hpx; exact hpx.2
      subst hx
      rw [List.filter_cons_of_neg (by simp; omega)]
      have hi' : ResidInv { st with pads := st.pads + 1 } vs := hi
      split at h
      · exact ih _ _ _ h hq hi'
      · split at h
        · exact ih _ _ _ h hq hi'
        · split at h
          · rename_i hq1
            injection h with h
            subst h
            exact absurd hq1 hq
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
        · have := ih _ _ _ h hq (decStep_inv st vs (c.tbl x) hi)
          simpa using this

/-- `canonical=True` is `canonical=False` and one more check: a result whose last group leaves non-zero
bits after its last whole byte is refused with "Non-zero padding bits", for every other option. The
bits are those of the last data character, whose value is its index in the alphabet. -/
def B64CanonicalLaw : Prop :=
  ∀ (s : List Nat) (strict : Option Bool) (p : Bool) (alpha : AlphaArg) (g : Option (List Nat)),
    a2bB64 (.bytes s) strict p alpha (g.map .bytes) true =
      (a2bB64 (.bytes s) strict p alpha (g.map .bytes) false).bind (fun r =>
        if resid64 ((s.filter (fun x => decide (x ∈ alphaChars alpha) && x != 61)).map
            (revT (alphaChars alpha) (some 61))) ≠ 0
        then .error (err "Non-zero padding bits") else .ok r)

theorem b64CanonicalLaw_proven : B64CanonicalLaw := by
  intro s strict p alpha g
  rcases a2bB64_cases alpha with ⟨e, he⟩ | ⟨hA, he⟩
  · rw [he, he]; rfl
  · rw [he, he]
    have h61 := tbl64_61 _ hA
    rw [core_slow _ h61, core_slow _ h61]
    have hf : s.filter (fun x => decide (x ∈ alphaChars alpha) && x != 61) =
        s.filter (fun x => decide (revT (alphaChars alpha) (some 61) x < 64)) := by
      apply List.filter_congr
      intro x _
      have := tbl64_lt _ hA x
      by_cases h2 : x = 61
      · subst h2
        simp [Nat.not_lt.mpr h61]
      · by_cases h1 : x ∈ alphaChars alpha
        · simp [h1, h2, this.mpr ⟨h1, h2⟩]
        · have h3 : ¬ revT (alphaChars alpha) (some 61) x < 64 := fun h' => h1 (this.mp h').1
          simp [h1, h3]
    rw [hf]
    cases hs : slow64 ⟨strict.getD g.isSome, p, revT (alphaChars alpha) (some 61), igEff strict g⟩ s {} with
    | error e => rfl
    | ok st =>
      simp only [Except.bind]
      by_cases hq : st.quad = 1
      · simp [fin64, hq, bind, Except.bind, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]
      · have hinv := slow_resid _ h61 s {} st [] hs hq ⟨rfl, rfl⟩
        simp only [List.nil_append] at hinv
        rw [← hinv.2]
        unfold fin64
        simp only [hq, if_false]
        by_cases hpd : (p = true ∧ st.quad ≠ 0 ∧ st.quad + st.pads < 4)
        · simp [hpd, bind, Except.bind, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]
        · simp [hpd, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]

/-! ### An ignored `'='` before data -/

theorem slow_prefix (c : B64) (m1 m2 : List Nat) (h : ∀ st, slow64 c m1 st = slow64 c m2 st) :
    ∀ (s1 : List Nat) (st : Dec), slow64 c (s1 ++ m1) st = slow64 c (s1 ++ m2) st := by
  intro s1
  induction s1 with
  | nil => exact h
  | cons x xs ih =>
    intro st
    simp only [List.cons_append, slow64]
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
        · exact ih _

theorem slow_eq_data (c : B64) (hp : c.padded = true) (hign : (!c.strict || ign c.ig 61) = true)
    (h61 : 64 ≤ c.tbl 61) (y : Nat) (hy : c.tbl y < 64) (r : List Nat) (st : Dec) :
    slow64 c (61 :: y :: r) st = slow64 c (y :: r) st := by
  have hy61 : (y == 61) = false := by
    apply beq_false_of_ne; intro e; subst e; omega
  have hn : ¬ (c.strict = true ∧ ign c.ig 61 = false) := by
    intro ⟨h1, h2⟩
    simp [h1, h2] at hign
  have step : ∀ st' : Dec, slow64 c (y :: r) st' = slow64 c r (decStep { st' with pads := 0 } (c.tbl y)) := by
    intro st'
    simp only [slow64, hp, hy61, Bool.and_false, Bool.false_eq_true, if_false, if_neg (Nat.not_le.mpr hy)]
    rw [if_neg]
    intro ⟨_, h1, h2⟩
    exact hn ⟨h1, by simpa using h2⟩
  have lhs : slow64 c (61 :: y :: r) st = slow64 c (y :: r) { st with pads := st.pads + 1 } := by
    rw [slow64]
    simp only [hp, beq_self_eq_true, Bool.and_self, if_true]
    split
    · rfl
    · first | rfl | rw [if_pos hign]
  rw [lhs, step, step]

/-- A `'='` that the decoding ignores (non-strict, or `'='` in `ignorechars`) and that a data character
follows can be taken out without changing anything: `padded=True`, any alphabet, any `canonical`. The
docs: with `'='` in `ignorechars`, "the pad characters presented before the end of the encoded data
... will be ignored". `a2b_base32` breaks the same statement (`B32PadBeforeDataIgnored`). -/
def B64PadBeforeDataIgnored : Prop :=
  ∀ (s1 s2 : List Nat) (y : Nat) (strict : Option Bool) (alpha : AlphaArg) (g : Option (List Nat)) (k : Bool),
    (strict.getD g.isSome = false ∨ ∃ l, g = some l ∧ 61 ∈ l) → y ∈ alphaChars alpha → y ≠ 61 →
    a2bB64 (.bytes (s1 ++ 61 :: y :: s2)) strict true alpha (g.map .bytes) k =
      a2bB64 (.bytes (s1 ++ y :: s2)) strict true alpha (g.map .bytes) k

theorem b64PadBeforeDataIgnored_proven : B64PadBeforeDataIgnored := by
  intro s1 s2 y strict alpha g k hg hy hy61
  rcases a2bB64_cases alpha with ⟨e, he⟩ | ⟨hA, he⟩
  · rw [he, he]
  · rw [he, he]
    have h61 := tbl64_61 _ hA
    rw [core_slow _ h61, core_slow _ h61]
    have hign : (!(strict.getD g.isSome) || ign (igEff strict g) 61) = true := by
      rcases hg with hg | ⟨l, rfl, hl⟩
      · simp [hg]
      · cases hs : strict.getD (some l).isSome with
        | false => rfl
        | true =>
          have hne : l ≠ [] := List.ne_nil_of_mem hl
          simp only [Option.isSome_some] at hs
          simp [igEff, hs, hne, ign, hl]
    rw [slow_prefix _ _ _ (fun st => slow_eq_data _ rfl hign h61 y ((tbl64_lt _ hA y).mpr ⟨hy, hy61⟩) s2 st) s1 {}]

/-! ### The encoder over every option -/

/-- `bytes.translate(bytes.maketrans(BASE64_ALPHABET, a))` on one byte. -/
def trAlpha (A : List Nat) (c : Nat) : Nat := if c ∈ b64Alpha then A.getD (b64Alpha.idxOf c) 0 else c

theorem b64_idx : ∀ v, v < 64 → b64Alpha.idxOf (b64Alpha.getD v 0) = v ∧ b64Alpha.getD v 0 ∈ b64Alpha := by
  decide +kernel

theorem tr_getD (A : List Nat) (v : Nat) (hv : v < 64) : trAlpha A (b64Alpha.getD v 0) = A.getD v 0 := by
  obtain ⟨h1, h2⟩ := b64_idx v hv
  unfold trAlpha
  rw [if_pos h2, h1]

theorem fastEnc64_tr (A : List Nat) : ∀ (n : Nat) (d : List Nat), d.length ≤ n →
    fastEnc64 A d = ((fastEnc64 b64Alpha d).1.map (trAlpha A), (fastEnc64 b64Alpha d).2) := by
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
    | [_], _ => rfl
    | [_, _], _ => rfl
    | x :: y :: z :: r, h =>
      rw [fastEnc64_three, fastEnc64_three, ih r (by simp at h; omega)]
      simp only [List.cons_append, List.nil_append, List.map_cons]
      rw [tr_getD A _ (Nat.mod_lt _ (by decide)), tr_getD A _ (Nat.mod_lt _ (by decide)),
        tr_getD A _ (Nat.mod_lt _ (by decide)), tr_getD A _ (Nat.mod_lt _ (by decide))]

theorem tail64_tr (A r : List Nat) : tail64 A r = (tail64 b64Alpha r).map (trAlpha A) := by
  match r with
  | [] => rfl
  | [_] =>
    simp only [tail64, List.map_cons, List.map_nil]
    rw [tr_getD A _ (Nat.mod_lt _ (by decide)), tr_getD A _ (Nat.mod_lt _ (by decide))]
  | [_, _] =>
    simp only [tail64, List.map_cons, List.map_nil]
    rw [tr_getD A _ (Nat.mod_lt _ (by decide)), tr_getD A _ (Nat.mod_lt _ (by decide)),
      tr_getD A _ (Nat.mod_lt _ (by decide))]
  | _ :: _ :: _ :: _ => rfl

theorem unwrapped64_tr (A d : List Nat) (p : Bool) :
    unwrapped64 A d p = (unwrapped64 b64Alpha d p).map (trAlpha A) := by
  have h61 : trAlpha A 61 = 61 := by simp [trAlpha, show (61 : Nat) ∉ b64Alpha by decide +kernel]
  simp only [unwrapped64, List.map_append, fastEnc64_tr A d.length d (Nat.le_refl _), tail64_tr A,
    List.map_replicate, h61]

theorem unwrapped64_strip (d : List Nat) (p : Bool) :
    (unwrapped64 b64Alpha d true).filter (fun c => p || c != 61) = unwrapped64 b64Alpha d p := by
  cases p with
  | true => simp
  | false =>
    have hm := unwrapped64_mem b64Alpha (by decide) d false
    simp only [unwrapped64, Bool.false_eq_true, if_false, if_true, List.replicate_zero, List.append_nil,
      Bool.false_or] at hm ⊢
    have hr : (List.replicate (pads64 d.length) 61).filter (fun c => c != 61) = [] := by
      simp [List.filter_eq_nil_iff]
    rw [List.filter_append _ (List.replicate _ _), hr, List.append_nil]
    apply List.filter_eq_self.mpr
    intro x hx
    rcases hm x hx with h | ⟨_, h⟩
    · have : x ≠ 61 := fun e => (show (61 : Nat) ∉ b64Alpha by decide +kernel) (e ▸ h)
      simpa using this
    · cases h

/-- `b2a_base64` over every option, against the specification encoder at its defaults (`b2aBase64`,
which `base64RoundTrip_proven` and `b2aLength_proven` pin): `padded=False` drops the `'='`, `alphabet`
is `translate` from the standard alphabet, a non-zero `wrapcol` is rounded to a multiple of 4 (at least 4)
and the lines are cut by `wraplines`, and `newline` adds one `'\n'`. Then the refusals, in their order:
a negative or too large `wrapcol`, then an alphabet that is not 64 bytes. -/
def B2a64OptionLaw : Prop :=
  (∀ (d : List Nat) (p : Bool) (w : Nat) (nl : Bool) (alpha : Option (List Nat)),
    (∀ x ∈ d, x < 256) → w < 2 ^ 64 → (∀ a, alpha = some a → a.length = 64) →
    b2aB64 (.bytes d) p w nl (alpha.map .bytes) =
      .ok (let s := ((b2aBase64 d false).filter (fun c => p || c != 61)).map (trAlpha (alpha.getD b64Alpha))
           let w' := if w = 0 then 0 else if w < 4 then 4 else w / 4 * 4
           (if w' = 0 then s else wraplinesC s w') ++ (if nl then [10] else []))) ∧
  (∀ (d : List Nat) (p : Bool) (w : Int) (nl : Bool) (alpha : Option Data), w < 0 →
    b2aB64 (.bytes d) p w nl alpha = .error (.valueError "Cannot convert negative int")) ∧
  (∀ (d : List Nat) (p : Bool) (w : Int) (nl : Bool) (alpha : Option Data), 2 ^ 64 ≤ w →
    b2aB64 (.bytes d) p w nl alpha = .error (.overflowError "Python int too large for C size_t")) ∧
  (∀ (d : List Nat) (p : Bool) (w : Nat) (nl : Bool) (a : List Nat), w < 2 ^ 64 → a.length ≠ 64 →
    b2aB64 (.bytes d) p w nl (some (.bytes a)) = .error (.valueError "alphabet must have length 64"))

theorem b2a64OptionLaw_proven : B2a64OptionLaw := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d p w nl alpha hd hw ha
    have hs : sizeT (w : Int) = .ok w := by
      simp only [sizeT]
      rw [if_neg (by omega), if_neg (by omega)]
      rfl
    have h0 : b2aBase64 d false = unwrapped64 b64Alpha d true := by
      rw [← b2a64Core_eq d hd false]
      simp [b2a64Core, unwrapped64, pads64]
    obtain ⟨A, hA, hAeq⟩ : ∃ A, encTable alpha b64Alpha 64 = .ok A ∧ alpha.getD b64Alpha = A := by
      cases alpha with
      | none => exact ⟨b64Alpha, rfl, rfl⟩
      | some a => exact ⟨a, by simp [encTable, ha a rfl], rfl⟩
    have hb : bufOpt (alpha.map .bytes) = .ok alpha := by cases alpha <;> rfl
    simp only [b2aB64, bufData, hs, hb, hA, bind, Except.bind, pure, Except.pure]
    rw [hAeq, h0, unwrapped64_strip, ← unwrapped64_tr]
    simp only [b2a64Core, unwrapped64, pads64]
    by_cases hw0 : w = 0
    · subst hw0; cases nl <;> simp
    · have hpos : (if w < 4 then 4 else w / 4 * 4) ≠ 0 := by split <;> omega
      cases nl <;> simp [hw0, hpos]
  · intro d p w nl alpha hw
    simp [b2aB64, bufData, sizeT, hw, bind, Except.bind]
  · intro d p w nl alpha hw
    have : ¬ w < 0 := by omega
    simp only [b2aB64, bufData, sizeT, if_neg this, if_pos hw, bind, Except.bind]
  · intro d p w nl a hw ha
    have hs : sizeT (w : Int) = .ok w := by
      simp only [sizeT]
      rw [if_neg (by omega), if_neg (by omega)]
      rfl
    simp only [b2aB64, bufData, hs, bufOpt, encTable, bind, Except.bind, pure, Except.pure]
    rw [if_pos ha]
    rfl

end PyLean.TextLibs.Binascii
