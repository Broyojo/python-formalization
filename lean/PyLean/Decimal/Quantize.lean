import PyLean.Decimal.Compare

/-!
`quantize` and `to_integral_exact`: the result is the correctly rounded value at
the requested exponent, InvalidOperation signals exactly that the result does
not fit, and Inexact signals exactly that the value changed.
-/

namespace PyLean.Decimal

open PyLean

/-! ## The flag monad -/

theorem bind_ok {α β : Type} {x : DM α} {f : α → DM β} {fl : List Signal} {r : β × List Signal}
    (h : (x >>= f).run fl = .ok r) :
    ∃ a fl1, x.run fl = .ok (a, fl1) ∧ (f a).run fl1 = .ok r := by
  simp only [StateT.run, bind, StateT.bind, Except.bind] at h ⊢
  cases hx : x fl with
  | error e => rw [hx] at h; cases h
  | ok p => rw [hx] at h; exact ⟨p.1, p.2, rfl, h⟩

theorem pure_ok {α : Type} {a : α} {fl : List Signal} {r : α × List Signal}
    (h : (pure a : DM α).run fl = .ok r) : r = (a, fl) := by
  simp only [StateT.run, pure, StateT.pure, Except.pure] at h
  cases h; rfl

/-- A signal that did not raise is flagged, and nothing else changes. -/
theorem raiseSig_ok {c : Ctx} {s : Signal} {fl fl' : List Signal} {u : Unit}
    (h : (raiseSig c s).run fl = .ok (u, fl')) :
    s ∉ c.traps ∧ ∀ t, t ∈ fl' ↔ t ∈ fl ∨ t = s := by
  have hb : ∀ fl1, (modify (fun fl => if s ∈ fl then fl else fl ++ [s]) : DM Unit).run fl1 =
      .ok ((), if s ∈ fl1 then fl1 else fl1 ++ [s]) := fun _ => rfl
  simp only [raiseSig] at h
  obtain ⟨_, fl1, h1, h2⟩ := bind_ok h
  rw [hb] at h1
  cases h1
  by_cases ht : s ∈ c.traps
  · simp only [ht, ↓reduceIte] at h2
    cases h2
  · simp only [ht, ↓reduceIte] at h2
    have := pure_ok h2
    cases this
    refine ⟨ht, fun t => ?_⟩
    by_cases hs : s ∈ fl
    · simp only [hs, ↓reduceIte]
      constructor
      · exact Or.inl
      · rintro (h | rfl)
        · exact h
        · exact hs
    · simp [hs]

theorem liftPy_ok {α : Type} {x : Py α} {fl fl' : List Signal} {a : α}
    (h : (liftPy x).run fl = .ok (a, fl')) : x = .ok a ∧ fl' = fl := by
  cases hx : x with
  | error e => subst hx; cases h
  | ok v =>
    subst hx
    simp only [liftPy, StateT.run, Functor.map, Except.map] at h
    cases h
    exact ⟨rfl, rfl⟩

theorem invalid_ok {c : Ctx} {fl fl' : List Signal} {d : Dec}
    (h : (invalid c).run fl = .ok (d, fl')) :
    d = .nan false false 0 ∧ Signal.invalidOperation ∈ fl' ∧
      ∀ t, t ≠ .invalidOperation → (t ∈ fl' ↔ t ∈ fl) := by
  simp only [invalid] at h
  obtain ⟨u, fl1, h1, h2⟩ := bind_ok h
  have := pure_ok h2
  cases this
  obtain ⟨_, hm⟩ := raiseSig_ok h1
  refine ⟨rfl, (hm _).mpr (Or.inr rfl), fun t ht => ?_⟩
  rw [hm t]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h ht
  · exact Or.inl

/-! ## `_fix` on a value that already fits -/

/-- The exponent `_fix` leaves a value with that fits the context:
fold-down to `Etop` under `clamp`. -/
def foldExp (c : Ctx) (x : Int) : Int := if c.clamp then min x c.etop else x

theorem fix_fits (c : Ctx) (neg : Bool) (co : Nat) (x : Int) (fl fl' : List Signal) (d : Dec)
    (h1 : numDigits co ≤ c.prec) (h2 : x + numDigits co - 1 ≤ c.emax) (h3 : c.etiny ≤ x)
    (hok : (fix c (.fin neg co x)).run fl = .ok (d, fl')) :
    d = .fin neg (co * 10 ^ (x - foldExp c x).toNat) (foldExp c x) ∧
      (Signal.inexact ∈ fl' ↔ Signal.inexact ∈ fl) ∧ (Signal.rounded ∈ fl' ↔ Signal.rounded ∈ fl) := by
  simp only [fix] at hok
  by_cases hc : co = 0
  · subst hc
    have hn : numDigits 0 = 1 := numDigits_zero
    rw [hn] at h2
    simp only [↓reduceIte] at hok
    have hx : min (max x c.etiny) (if c.clamp = true then c.etop else c.emax) = foldExp c x := by
      unfold foldExp
      cases hcl : c.clamp <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    rw [hx] at hok
    have hz : ∀ k, 0 * 10 ^ k = 0 := fun k => Nat.zero_mul _
    split at hok
    · obtain ⟨_, fl1, h4, h5⟩ := bind_ok hok
      have h6 := pure_ok h5
      cases h6
      obtain ⟨_, hm⟩ := raiseSig_ok h4
      refine ⟨by rw [hz], ?_, ?_⟩ <;> simp [hm]
    · rename_i hne
      have h6 := pure_ok hok
      cases h6
      have he : foldExp c x = x := by simpa using hne
      refine ⟨by rw [hz, he], Iff.rfl, Iff.rfl⟩
  · simp only [hc, ↓reduceIte] at hok
    have hp : (numDigits co : Int) + x - c.prec ≤ c.etop := by
      simp only [Ctx.etop]; omega
    rw [if_neg (by omega)] at hok
    have hnr : ¬ x < (if decide ((numDigits co : Int) + x - c.prec < c.etiny) = true then c.etiny
        else (numDigits co : Int) + x - c.prec) := by
      split <;> omega
    rw [if_neg hnr] at hok
    have tail : ∀ fl0, (if c.clamp = true ∧ x > c.etop then
          (do raiseSig c Signal.clamped; pure (Dec.fin neg (co * 10 ^ (x - c.etop).toNat) c.etop) : DM Dec)
        else pure (Dec.fin neg co x)).run fl0 = .ok (d, fl') →
        d = .fin neg (co * 10 ^ (x - foldExp c x).toNat) (foldExp c x) ∧
          (Signal.inexact ∈ fl' ↔ Signal.inexact ∈ fl0) ∧ (Signal.rounded ∈ fl' ↔ Signal.rounded ∈ fl0) := by
      intro fl0 h
      split at h
      · rename_i hcl
        obtain ⟨_, fl1, h4, h5⟩ := bind_ok h
        have h6 := pure_ok h5
        cases h6
        obtain ⟨_, hm⟩ := raiseSig_ok h4
        have he : foldExp c x = c.etop := by
          simp only [foldExp, hcl.1, ↓reduceIte]; omega
        refine ⟨by rw [he], ?_, ?_⟩ <;> simp [hm]
      · rename_i hcl
        have h6 := pure_ok h
        cases h6
        have he : foldExp c x = x := by
          unfold foldExp
          cases hc2 : c.clamp
          · rfl
          · simp only [↓reduceIte]
            have : ¬ x > c.etop := fun hg => hcl ⟨hc2, hg⟩
            omega
        refine ⟨by simp [he], Iff.rfl, Iff.rfl⟩
    split at hok
    · obtain ⟨_, fl1, h4, h5⟩ := bind_ok hok
      obtain ⟨_, hm⟩ := raiseSig_ok h4
      obtain ⟨h7, h8, h9⟩ := tail fl1 h5
      refine ⟨h7, ?_, ?_⟩
      · rw [h8]; simp [hm]
      · rw [h9]; simp [hm]
    · exact tail fl hok

/-! ## Digit bounds -/

theorem le_numDigits {x j : Nat} (h : 10 ^ j ≤ x) : j + 1 ≤ numDigits x := by
  rcases Nat.lt_or_ge (numDigits x) (j + 1) with hlt | hge
  · have h1 := lt_pow_numDigits x
    have h2 : 10 ^ numDigits x ≤ 10 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · exact hge

theorem roundSpec_ge (m : Rounding) (neg : Bool) (q r b : Nat) : q ≤ roundSpec m neg q r b := by
  cases m <;> simp only [roundSpec] <;> (try split) <;> omega

theorem roundSpec_le (m : Rounding) (neg : Bool) (q r b : Nat) : roundSpec m neg q r b ≤ q + 1 := by
  cases m <;> simp only [roundSpec] <;> (try split) <;> omega

theorem roundSpec_exact (m : Rounding) (neg : Bool) (q b : Nat) (hb : 0 < b) :
    roundSpec m neg q 0 b = q := by
  cases m <;> simp [roundSpec] <;> omega

/-! ## The specification of `quantize` -/

/-- The coefficient of `±co·10^e` at exponent `qe`: padded with zeros, or
rounded by `roundSpec` on the dropped digits. -/
def quantSpec (m : Rounding) (neg : Bool) (co : Nat) (e qe : Int) : Nat :=
  if e ≥ qe then co * 10 ^ (e - qe).toNat
  else roundSpec m neg (co / 10 ^ (qe - e).toNat) (co % 10 ^ (qe - e).toNat) (10 ^ (qe - e).toNat)

/-- For a non-zero operand, the result has at least the digits the source's
early check counts, `adjusted - qe + 1`. -/
theorem quantSpec_digits (m : Rounding) (neg : Bool) (co : Nat) (e qe : Int) (hc : co ≠ 0) :
    e + numDigits co - 1 - qe + 1 ≤ numDigits (quantSpec m neg co e qe) := by
  have hl := pow_numDigits_le hc
  have hn := numDigits_pos co
  unfold quantSpec
  split
  · rename_i he
    have : 10 ^ (numDigits co - 1 + (e - qe).toNat) ≤ co * 10 ^ (e - qe).toNat := by
      rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ hl
    have := le_numDigits this
    omega
  · rename_i he
    generalize hK : (qe - e).toNat = K
    have hge := roundSpec_ge m neg (co / 10 ^ K) (co % 10 ^ K) (10 ^ K)
    generalize roundSpec m neg (co / 10 ^ K) (co % 10 ^ K) (10 ^ K) = q' at hge ⊢
    have hq' := numDigits_pos q'
    by_cases hk : numDigits co ≤ K
    · omega
    · have h1 : 10 ^ (numDigits co - 1 - K) ≤ co / 10 ^ K := by
        rw [Nat.le_div_iff_mul_le (Nat.pow_pos (by decide)), ← Nat.pow_add]
        rw [show numDigits co - 1 - K + K = numDigits co - 1 by omega]
        exact hl
      have := le_numDigits (Nat.le_trans h1 hge)
      omega

theorem quantSpec_zero (m : Rounding) (neg : Bool) (e qe : Int) : quantSpec m neg 0 e qe = 0 := by
  unfold quantSpec
  split
  · exact Nat.zero_mul _
  · rw [Nat.zero_div, Nat.zero_mod]
    exact roundSpec_exact m neg 0 _ (Nat.pow_pos (by decide))

theorem rescale_quantSpec (m : Rounding) (neg : Bool) (co : Nat) (e qe : Int) (hc : co ≠ 0)
    {r : Dec} (h : rescale (.fin neg co e) qe m = .ok r) :
    r = .fin neg (quantSpec m neg co e qe) qe := by
  unfold quantSpec
  split
  · rename_i he
    simp only [rescale, hc, ↓reduceIte, he] at h
    cases h; rfl
  · rename_i he
    rcases rescale_round m neg co e qe hc (by omega) with h2 | ⟨msg, h2⟩
    · rw [h2] at h; cases h; rfl
    · rw [h2] at h; cases h

/-- `cmpVal` of the rounded result against the operand: unchanged exactly when
the dropped digits are all zero. -/
theorem cmpVal_quantized (m : Rounding) (neg : Bool) (co : Nat) (e qe : Int) (hc : co ≠ 0) (he : e < qe) :
    cmpVal (.fin neg (quantSpec m neg co e qe) qe) (.fin neg co e) = .eq ↔
      co % 10 ^ (qe - e).toNat = 0 := by
  have hq : quantSpec m neg co e qe =
      roundSpec m neg (co / 10 ^ (qe - e).toNat) (co % 10 ^ (qe - e).toNat) (10 ^ (qe - e).toNat) := by
    simp only [quantSpec, show ¬ e ≥ qe by omega, ↓reduceIte]
  rw [hq, cmpVal_fin_eq]
  have hA : (qe - min qe e).toNat = (qe - e).toNat := by omega
  have hB : (e - min qe e).toNat = 0 := by omega
  rw [hA, hB, Nat.pow_zero, Nat.mul_one]
  generalize (qe - e).toNat = K
  have hpos : 0 < 10 ^ K := Nat.pow_pos (by decide)
  have hdm := Nat.div_add_mod co (10 ^ K)
  have hge := roundSpec_ge m neg (co / 10 ^ K) (co % 10 ^ K) (10 ^ K)
  have hle := roundSpec_le m neg (co / 10 ^ K) (co % 10 ^ K) (10 ^ K)
  have hlt := Nat.mod_lt co hpos
  constructor
  · rintro (⟨_, h2⟩ | ⟨h1, _, h2⟩)
    · exact absurd h2 hc
    · rw [← h2]; exact Nat.mul_mod_left _ _
  · intro hr
    right
    rw [hr, roundSpec_exact m neg _ _ hpos]
    rw [hr] at hdm
    have hq0 : co / 10 ^ K ≠ 0 := by
      intro h0; rw [h0] at hdm; simp at hdm; exact hc hdm.symm
    refine ⟨hq0, rfl, ?_⟩
    rw [Nat.mul_comm]; omega

/-- For every context (`prec ≥ 1`, the type invariant) and all finite operands,
when `quantize` returns: the value `q'` that rounding (or padding) prescribes
"fits" if the target exponent is within `[Etiny, Emax]` and `q'` has at most
`prec` digits and adjusted exponent at most `Emax`. If it fits, the result
is that value at the target exponent (folded down to `Etop` under `clamp`,
which keeps the value) and Inexact is set exactly when non-zero digits were
dropped. If it does not fit, the result is NaN and InvalidOperation is set. -/
def QuantizeCorrect : Prop :=
  ∀ (c : Ctx) (r : Option Rounding) (neg : Bool) (co : Nat) (e : Int) (qn : Bool) (qc : Nat) (qe : Int)
    (fl fl' : List Signal) (d : Dec),
    1 ≤ c.prec →
    (quantize c (.fin neg co e) (.fin qn qc qe) r).run fl = .ok (d, fl') →
    let q' := quantSpec (r.getD c.rounding) neg co e qe
    let fits := c.etiny ≤ qe ∧ qe ≤ c.emax ∧ numDigits q' ≤ c.prec ∧ qe + numDigits q' - 1 ≤ c.emax
    (fits → d = .fin neg (q' * 10 ^ (qe - foldExp c qe).toNat) (foldExp c qe) ∧
      (Signal.inexact ∈ fl' ↔ Signal.inexact ∈ fl ∨ (e < qe ∧ co % 10 ^ (qe - e).toNat ≠ 0))) ∧
    (¬fits → d = .nan false false 0 ∧ Signal.invalidOperation ∈ fl')

theorem invalid_pure {c : Ctx} {fl fl' : List Signal} {d : Dec}
    (h : (invalid c).run fl = .ok (d, fl')) :
    d = .nan false false 0 ∧ Signal.invalidOperation ∈ fl' := by
  obtain ⟨h3, h4, _⟩ := invalid_ok h
  exact ⟨h3, h4⟩

theorem quantizeFlags_ok (c : Ctx) (m : Rounding) (neg : Bool) (co : Nat) (e qe : Int) (hc : co ≠ 0)
    (fl fl' : List Signal) (d : Dec)
    (h1 : numDigits (quantSpec m neg co e qe) ≤ c.prec)
    (h2 : qe + numDigits (quantSpec m neg co e qe) - 1 ≤ c.emax) (h3 : c.etiny ≤ qe)
    (h : (quantizeFlags c (.fin neg (quantSpec m neg co e qe) qe) qe neg co e).run fl = .ok (d, fl')) :
    d = .fin neg (quantSpec m neg co e qe * 10 ^ (qe - foldExp c qe).toNat) (foldExp c qe) ∧
      (Signal.inexact ∈ fl' ↔ Signal.inexact ∈ fl ∨ (e < qe ∧ co % 10 ^ (qe - e).toNat ≠ 0)) := by
  simp only [quantizeFlags] at h
  split at h
  · rename_i he
    have heq := cmpVal_quantized m neg co e qe hc (by omega)
    split at h
    · rename_i hne
      have hr0 : co % 10 ^ (qe - e).toNat ≠ 0 := fun h0 => hne (heq.mpr h0)
      obtain ⟨_, fl1, a1, a2⟩ := bind_ok h
      obtain ⟨_, fl2, a3, a4⟩ := bind_ok a2
      obtain ⟨_, m1⟩ := raiseSig_ok a1
      obtain ⟨_, m2⟩ := raiseSig_ok a3
      obtain ⟨f1, f2, _⟩ := fix_fits c neg _ qe fl2 fl' d h1 h2 h3 a4
      refine ⟨f1, ?_⟩
      rw [f2, m2, m1]
      simp [show e < qe by omega, hr0]
    · rename_i hne
      have hr0 : co % 10 ^ (qe - e).toNat = 0 := heq.mp (by simpa using hne)
      obtain ⟨_, fl1, a1, a2⟩ := bind_ok h
      obtain ⟨_, m1⟩ := raiseSig_ok a1
      obtain ⟨f1, f2, _⟩ := fix_fits c neg _ qe fl1 fl' d h1 h2 h3 a2
      refine ⟨f1, ?_⟩
      rw [f2, m1]
      simp [hr0]
  · rename_i he
    obtain ⟨f1, f2, _⟩ := fix_fits c neg _ qe fl fl' d h1 h2 h3 h
    refine ⟨f1, ?_⟩
    rw [f2]
    constructor
    · exact Or.inl
    · rintro (h5 | ⟨h5, _⟩)
      · exact h5
      · omega

theorem quantizeCorrect_proven : QuantizeCorrect := by
  intro c r neg co e qn qc qe fl fl' d hp h q' fits
  have hbad : (d = .nan false false 0 ∧ Signal.invalidOperation ∈ fl') → ¬fits →
      (fits → d = .fin neg (q' * 10 ^ (qe - foldExp c qe).toNat) (foldExp c qe) ∧
        (Signal.inexact ∈ fl' ↔ Signal.inexact ∈ fl ∨ (e < qe ∧ co % 10 ^ (qe - e).toNat ≠ 0))) ∧
      (¬fits → d = .nan false false 0 ∧ Signal.invalidOperation ∈ fl') :=
    fun hn hf => ⟨fun h' => absurd h' hf, fun _ => hn⟩
  have hgood : (fits → d = .fin neg (q' * 10 ^ (qe - foldExp c qe).toNat) (foldExp c qe) ∧
        (Signal.inexact ∈ fl' ↔ Signal.inexact ∈ fl ∨ (e < qe ∧ co % 10 ^ (qe - e).toNat ≠ 0))) →
      fits → _ := fun hg hf => (⟨hg, fun hn => absurd hf hn⟩ :
        (fits → d = .fin neg (q' * 10 ^ (qe - foldExp c qe).toNat) (foldExp c qe) ∧
          (Signal.inexact ∈ fl' ↔ Signal.inexact ∈ fl ∨ (e < qe ∧ co % 10 ^ (qe - e).toNat ≠ 0))) ∧
        (¬fits → d = .nan false false 0 ∧ Signal.invalidOperation ∈ fl'))
  have hrun : quantize c (.fin neg co e) (.fin qn qc qe) r =
      quantizeFin c (r.getD c.rounding) neg co e qe := rfl
  rw [hrun] at h
  unfold quantizeFin at h
  by_cases hr : c.etiny ≤ qe ∧ qe ≤ c.emax
  · rw [if_neg (fun hn => hn hr)] at h
    by_cases hc : co = 0
    · subst hc
      simp only [↓reduceIte] at h
      have hq0 : q' = 0 := quantSpec_zero _ _ _ _
      have hn0 : numDigits 0 = 1 := numDigits_zero
      have hf : fits := by
        simp only [fits, hq0, hn0]
        exact ⟨hr.1, hr.2, hp, by omega⟩
      obtain ⟨h3, h4, _⟩ := fix_fits c neg 0 qe fl fl' d (by omega) (by omega) hr.1 h
      refine hgood (fun _ => ⟨?_, ?_⟩) hf
      · rw [h3, hq0]
      · rw [h4]
        constructor
        · exact Or.inl
        · rintro (h5 | ⟨_, h5⟩)
          · exact h5
          · exact absurd (Nat.zero_mod _) h5
    · simp only [hc, ↓reduceIte] at h
      have hdig := quantSpec_digits (r.getD c.rounding) neg co e qe hc
      by_cases hA : adjustedD co e > c.emax
      · rw [if_pos hA] at h
        have hA' : e + (numDigits co : Int) - 1 > c.emax := hA
        exact hbad (invalid_pure h) (fun hf => by
          obtain ⟨_, _, _, h4⟩ := hf
          simp only [q'] at h4
          omega)
      rw [if_neg hA] at h
      have hA' : ¬ e + (numDigits co : Int) - 1 > c.emax := hA
      by_cases hB : adjustedD co e - qe + 1 > c.prec
      · rw [if_pos hB] at h
        have hB' : e + (numDigits co : Int) - 1 - qe + 1 > c.prec := hB
        exact hbad (invalid_pure h) (fun hf => by
          obtain ⟨_, _, h3, _⟩ := hf
          simp only [q'] at h3
          omega)
      rw [if_neg hB] at h
      obtain ⟨ans, fl1, h1, h2⟩ := bind_ok h
      obtain ⟨hres, rfl⟩ := liftPy_ok h1
      have hans := rescale_quantSpec _ neg co e qe hc hres
      subst hans
      simp only at h2
      by_cases hC : adjustedD q' qe > c.emax
      · rw [if_pos hC] at h2
        have hC' : qe + (numDigits q' : Int) - 1 > c.emax := hC
        exact hbad (invalid_pure h2) (fun hf => by
          obtain ⟨_, _, _, h4⟩ := hf
          omega)
      rw [if_neg hC] at h2
      have hC' : ¬ qe + (numDigits q' : Int) - 1 > c.emax := hC
      by_cases hD : numDigits q' > c.prec
      · rw [if_pos hD] at h2
        exact hbad (invalid_pure h2) (fun hf => by
          obtain ⟨_, _, h4, _⟩ := hf
          omega)
      rw [if_neg hD] at h2
      have hf : fits := ⟨hr.1, hr.2, Nat.not_lt.mp hD, Int.not_lt.mp hC'⟩
      refine hgood (fun _ => ?_) hf
      by_cases hE : q' ≠ 0 ∧ adjustedD q' qe < c.emin
      · rw [if_pos hE] at h2
        obtain ⟨_, fl2, a1, a2⟩ := bind_ok h2
        obtain ⟨_, m1⟩ := raiseSig_ok a1
        obtain ⟨g1, g2⟩ := quantizeFlags_ok c _ neg co e qe hc fl2 fl' d hf.2.2.1 hf.2.2.2 hr.1 a2
        refine ⟨g1, ?_⟩
        rw [g2, m1]
        simp
      · rw [if_neg hE] at h2
        exact quantizeFlags_ok c _ neg co e qe hc _ fl' d hf.2.2.1 hf.2.2.2 hr.1 h2
  · rw [if_pos (by simpa using hr)] at h
    exact hbad (invalid_pure h) (fun hf => hr ⟨hf.1, hf.2.1⟩)

/-- For every context, rounding argument and finite non-zero value with
`e < 0`, when `to_integral_exact` returns, the result is the correctly rounded
integer at exponent 0, Rounded is set, and Inexact is set exactly when non-zero
digits were dropped (docs: "signaling Inexact or Rounded as appropriate if
rounding occurs"; the source raises Rounded even when the dropped digits are
zeros, _pydecimal.py:2659, and so does libmpdec). -/
def ToIntegralExactCorrect : Prop :=
  ∀ (c : Ctx) (r : Option Rounding) (neg : Bool) (co : Nat) (e : Int) (fl fl' : List Signal) (d : Dec),
    e < 0 → co ≠ 0 →
    (toIntegralExact c (.fin neg co e) r).run fl = .ok (d, fl') →
    d = .fin neg (quantSpec (r.getD c.rounding) neg co e 0) 0 ∧ Signal.rounded ∈ fl' ∧
      (Signal.inexact ∈ fl' ↔ Signal.inexact ∈ fl ∨ co % 10 ^ (0 - e).toNat ≠ 0)

theorem toIntegralExactCorrect_proven : ToIntegralExactCorrect := by
  intro c r neg co e fl fl' d he hc h
  simp only [toIntegralExact, show ¬ e ≥ 0 by omega, ↓reduceIte, hc] at h
  obtain ⟨ans, fl1, h1, h2⟩ := bind_ok h
  obtain ⟨hres, rfl⟩ := liftPy_ok h1
  have hans := rescale_quantSpec _ neg co e 0 hc hres
  subst hans
  have heq := cmpVal_quantized (r.getD c.rounding) neg co e 0 hc he
  by_cases hne : cmpVal (.fin neg (quantSpec (r.getD c.rounding) neg co e 0) 0) (.fin neg co e) ≠ .eq
  · rw [if_pos hne] at h2
    have hr0 : co % 10 ^ (0 - e).toNat ≠ 0 := fun h0 => hne (heq.mpr h0)
    obtain ⟨_, fl2, a1, a2⟩ := bind_ok h2
    obtain ⟨_, fl3, a3, a4⟩ := bind_ok a2
    have := pure_ok a4
    cases this
    obtain ⟨_, m1⟩ := raiseSig_ok a1
    obtain ⟨_, m2⟩ := raiseSig_ok a3
    refine ⟨rfl, (m2 _).mpr (Or.inr rfl), ?_⟩
    rw [m2, m1]
    rw [Int.zero_sub] at hr0
    simp [hr0]
  · rw [if_neg hne] at h2
    have hr0 : co % 10 ^ (0 - e).toNat = 0 := heq.mp (by simpa using hne)
    obtain ⟨_, fl3, a3, a4⟩ := bind_ok h2
    have := pure_ok a4
    cases this
    obtain ⟨_, m2⟩ := raiseSig_ok a3
    refine ⟨rfl, (m2 _).mpr (Or.inr rfl), ?_⟩
    rw [m2]
    rw [Int.zero_sub] at hr0
    simp [hr0]

end PyLean.Decimal
