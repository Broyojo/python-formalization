import PyLean.Decimal.Quantize

/-!
Multiplication: outside the subnormal and overflow ranges, `*` returns the exact
product correctly rounded to `prec` digits, with the matching flags.
-/

namespace PyLean.Decimal

open PyLean

/-- `co·10^e` rounded to `prec` digits: nothing is dropped when `co` has at
most `prec` digits; otherwise the last `k` digits are dropped as `roundSpec`
says, and a carry to `10^prec` is renormalized to `10^(prec-1)` with the exponent
one higher. -/
def roundPrec (m : Rounding) (neg : Bool) (co : Nat) (e : Int) (prec : Nat) : Nat × Int :=
  if numDigits co ≤ prec then (co, e) else
  let k := numDigits co - prec
  let q' := roundSpec m neg (co / 10 ^ k) (co % 10 ^ k) (10 ^ k)
  if q' = 10 ^ prec then (10 ^ (prec - 1), e + k + 1) else (q', e + k)

theorem roundDir_cases (m : Rounding) (neg : Bool) (q r h : Nat) :
    roundDir m neg q r h = 1 ∨ roundDir m neg q r h = 0 ∨ roundDir m neg q r h = -1 := by
  cases m <;> cases neg <;> simp only [roundDir, Bool.not_true, Bool.not_false] <;>
    (repeat' split) <;> simp_all

/-- The kept prefix of a coefficient with more than `prec` digits has exactly
`prec` digits. -/
theorem prefix_bounds (co prec : Nat) (hc : co ≠ 0) (hp : 1 ≤ prec) (hn : prec < numDigits co) :
    10 ^ (prec - 1) ≤ co / 10 ^ (numDigits co - prec) ∧ co / 10 ^ (numDigits co - prec) < 10 ^ prec := by
  have hl := pow_numDigits_le hc
  have hu := lt_pow_numDigits co
  have hpos : 0 < 10 ^ (numDigits co - prec) := Nat.pow_pos (by decide)
  constructor
  · rw [Nat.le_div_iff_mul_le hpos, ← Nat.pow_add]
    rw [show prec - 1 + (numDigits co - prec) = numDigits co - 1 by omega]
    exact hl
  · rw [Nat.div_lt_iff_lt_mul hpos, ← Nat.pow_add]
    rw [show prec + (numDigits co - prec) = numDigits co by omega]
    exact hu

theorem numDigits_eq {x j : Nat} (h1 : 10 ^ (j - 1) ≤ x) (h2 : x < 10 ^ j) (hj : 1 ≤ j) : numDigits x = j := by
  have a := le_numDigits h1
  have b := (numDigits_le_iff hj).mpr h2
  omega

theorem fixFinish_ok (c : Ctx) (neg : Bool) (cf : Nat) (ef : Int) (ch : Int) (fl fl' : List Signal) (d : Dec)
    (he : ef ≤ c.etop) (h : (fixFinish c neg cf ef ch false).run fl = .ok (d, fl')) :
    d = .fin neg cf ef ∧ Signal.rounded ∈ fl' ∧
      (Signal.inexact ∈ fl' ↔ Signal.inexact ∈ fl ∨ ch ≠ 0) := by
  simp only [fixFinish] at h
  rw [if_neg (by omega)] at h
  simp only [pure_bind, Bool.false_eq_true, and_false, ↓reduceIte] at h
  have tail : ∀ fl0, (if isZero (Dec.fin neg cf ef) = true then
        (do raiseSig c Signal.clamped; pure (Dec.fin neg cf ef) : DM Dec)
      else pure (Dec.fin neg cf ef)).run fl0 = .ok (d, fl') →
      d = .fin neg cf ef ∧ ∀ t, t ≠ Signal.clamped → (t ∈ fl' ↔ t ∈ fl0) := by
    intro fl0 h0
    split at h0
    · obtain ⟨_, fl2, a1, a2⟩ := bind_ok h0
      have := pure_ok a2
      cases this
      obtain ⟨_, m⟩ := raiseSig_ok a1
      refine ⟨rfl, fun t ht => ?_⟩
      rw [m]
      simp [ht]
    · have := pure_ok h0
      cases this
      exact ⟨rfl, fun _ _ => Iff.rfl⟩
  split at h
  · rename_i hch
    obtain ⟨_, fl1, a1, a2⟩ := bind_ok h
    obtain ⟨_, fl2, a3, a4⟩ := bind_ok a2
    obtain ⟨_, m1⟩ := raiseSig_ok a1
    obtain ⟨_, m2⟩ := raiseSig_ok a3
    obtain ⟨t1, t2⟩ := tail fl2 a4
    refine ⟨t1, ?_, ?_⟩
    · rw [t2 _ (by decide), m2]; exact Or.inr rfl
    · rw [t2 _ (by decide), m2, m1]
      simp [hch]
  · rename_i hch
    obtain ⟨_, fl2, a3, a4⟩ := bind_ok h
    obtain ⟨_, m2⟩ := raiseSig_ok a3
    obtain ⟨t1, t2⟩ := tail fl2 a4
    refine ⟨t1, ?_, ?_⟩
    · rw [t2 _ (by decide), m2]; exact Or.inr rfl
    · rw [t2 _ (by decide), m2]
      simp [hch]

/-- The rounding branch of `_fix` when neither subnormal nor overflow is
involved. -/
theorem fixRound_normal (c : Ctx) (neg : Bool) (co : Nat) (e : Int) (fl fl' : List Signal) (d : Dec)
    (hc : co ≠ 0) (hp : 1 ≤ c.prec) (hn : c.prec < numDigits co)
    (hover : (roundPrec c.rounding neg co e c.prec).2 ≤ c.etop)
    (hok : (fixRound c neg co e ((numDigits co : Int) + e - c.prec) false).run fl = .ok (d, fl')) :
    d = .fin neg (roundPrec c.rounding neg co e c.prec).1 (roundPrec c.rounding neg co e c.prec).2 ∧
      Signal.rounded ∈ fl' ∧
      (Signal.inexact ∈ fl' ↔ Signal.inexact ∈ fl ∨ co % 10 ^ (numDigits co - c.prec) ≠ 0) := by
  have hfd : fixDigits co e ((numDigits co : Int) + e - c.prec) = (co, c.prec) := by
    have hdig : ((numDigits co : Int) + e - ((numDigits co : Int) + e - c.prec)) = c.prec := by omega
    simp only [fixDigits, hdig]
    rw [if_neg (by omega)]
    simp
  have hk1 : 1 ≤ numDigits co - c.prec := by omega
  obtain ⟨hlo, hhi⟩ := prefix_bounds co c.prec hc hp hn
  have hkv : ((numDigits co - c.prec : Nat) : Int) = (numDigits co : Int) - c.prec := by omega
  generalize hkk : numDigits co - c.prec = k at *
  have hr : co % 10 ^ k < 10 ^ k := Nat.mod_lt _ (Nat.pow_pos (by decide))
  have hb := pow_ten_eq_two_half hk1
  obtain ⟨hs, hz⟩ := roundDir_spec c.rounding neg (co / 10 ^ k) (co % 10 ^ k) (5 * 10 ^ (k - 1)) (by omega)
  rw [← hb] at hs
  have hcases := roundDir_cases c.rounding neg (co / 10 ^ k) (co % 10 ^ k) (5 * 10 ^ (k - 1))
  have hrp : roundPrec c.rounding neg co e c.prec =
      (if roundSpec c.rounding neg (co / 10 ^ k) (co % 10 ^ k) (10 ^ k) = 10 ^ c.prec
        then (10 ^ (c.prec - 1), e + k + 1)
        else (roundSpec c.rounding neg (co / 10 ^ k) (co % 10 ^ k) (10 ^ k), e + k)) := by
    simp only [roundPrec, Nat.not_le.mpr hn, ↓reduceIte, hkk]
  rw [hrp] at hover ⊢
  rw [← hs] at hover ⊢
  have hrk : roundKeep c.rounding neg co c.prec =
      (co / 10 ^ k, roundDir c.rounding neg (co / 10 ^ k) (co % 10 ^ k) (5 * 10 ^ (k - 1))) := by
    simp only [roundKeep, hkk]
  have hM : (numDigits co : Int) + e - c.prec = e + k := by omega
  rw [hM] at hok hfd
  simp only [fixRound, hfd, hrk] at hok
  obtain ⟨t, fl1, h1, h2⟩ := bind_ok hok
  generalize hch : roundDir c.rounding neg (co / 10 ^ k) (co % 10 ^ k) (5 * 10 ^ (k - 1)) = ch at *
  generalize hq : co / 10 ^ k = Q at *
  generalize hR : co % 10 ^ k = R at *
  -- the carry
  have hcarry : t = (if ch = 1 then (if Q + 1 = 10 ^ c.prec then (10 ^ (c.prec - 1), e + k + 1) else (Q + 1, e + k))
      else (Q, e + k)) ∧ fl1 = fl := by
    simp only [fixCarry] at h1
    by_cases h3 : ch > 0
    · have hone : ch = 1 := by omega
      rw [if_pos h3] at h1
      obtain ⟨q1, fl2, a1, a2⟩ := bind_ok h1
      obtain ⟨hinc, rfl⟩ := liftPy_ok a1
      rcases incr_cases Q c.prec with h4 | ⟨msg, h4⟩
      · rw [h4] at hinc
        cases hinc
        rw [hone, if_pos rfl]
        by_cases hca : Q + 1 = 10 ^ c.prec
        · have hbig : numDigits (Q + 1) > c.prec := by
            have := le_numDigits (x := Q + 1) (j := c.prec) (by omega)
            omega
          rw [if_pos hbig] at a2
          have := pure_ok a2
          cases this
          rw [if_pos hca]
          refine ⟨?_, rfl⟩
          rw [hca]
          have hdiv : 10 ^ c.prec / 10 = 10 ^ (c.prec - 1) := by
            obtain ⟨j, hj⟩ : ∃ j, c.prec = j + 1 := ⟨c.prec - 1, by omega⟩
            rw [hj, Nat.pow_succ, Nat.add_sub_cancel]
            exact Nat.mul_div_cancel _ (by decide)
          simp [hdiv]
        · have hsmall : ¬ numDigits (Q + 1) > c.prec := by
            have := (numDigits_le_iff (n := Q + 1) (k := c.prec) (by omega)).mpr (by omega)
            omega
          rw [if_neg hsmall] at a2
          have := pure_ok a2
          cases this
          rw [if_neg hca]
          exact ⟨rfl, rfl⟩
      · rw [h4] at hinc
        cases hinc
    · rw [if_neg h3] at h1
      have := pure_ok h1
      cases this
      rw [if_neg (by omega)]
      exact ⟨rfl, rfl⟩
  obtain ⟨ht, rfl⟩ := hcarry
  subst ht
  have hz0 : ch ≠ 0 ↔ R ≠ 0 := by
    constructor
    · intro a b; exact a (hz.mpr b)
    · intro a b; exact a (hz.mp b)
  by_cases hone : ch = 1
  · simp only [hone, ↓reduceIte] at hs hover h2 ⊢
    by_cases hca : Q + 1 = 10 ^ c.prec
    · simp only [hca, ↓reduceIte] at hover h2 ⊢
      obtain ⟨f1, f2, f3⟩ := fixFinish_ok c neg _ _ _ _ _ _ hover h2
      refine ⟨f1, f2, ?_⟩
      rw [f3]
      rw [hone] at hz0
      have : R ≠ 0 := hz0.mp (by decide)
      simp [this]
    · simp only [hca, ↓reduceIte] at hover h2 ⊢
      obtain ⟨f1, f2, f3⟩ := fixFinish_ok c neg _ _ _ _ _ _ hover h2
      refine ⟨f1, f2, ?_⟩
      rw [f3]
      rw [hone] at hz0
      have : R ≠ 0 := hz0.mp (by decide)
      simp [this]
  · simp only [hone, ↓reduceIte] at hs hover h2 ⊢
    have hQ : Q ≠ 10 ^ c.prec := by omega
    simp only [hQ, ↓reduceIte] at hover ⊢
    obtain ⟨f1, f2, f3⟩ := fixFinish_ok c neg _ _ _ _ _ _ hover h2
    refine ⟨f1, f2, ?_⟩
    rw [f3, hz0]

/-- `_fix` on a value in the normal range: the result is `co·10^e` rounded to
`prec` digits. A result that fits unrounded may be folded down under `clamp`. -/
theorem fix_normal (c : Ctx) (neg : Bool) (co : Nat) (e : Int) (fl fl' : List Signal) (d : Dec)
    (hc : co ≠ 0) (hp : 1 ≤ c.prec)
    (hmin : c.etiny ≤ e + (numDigits co - c.prec : Nat))
    (hover : (roundPrec c.rounding neg co e c.prec).2 + numDigits (roundPrec c.rounding neg co e c.prec).1 - 1 ≤ c.emax)
    (hok : (fix c (.fin neg co e)).run fl = .ok (d, fl')) :
    d = .fin neg ((roundPrec c.rounding neg co e c.prec).1 *
          10 ^ ((roundPrec c.rounding neg co e c.prec).2 - foldExp c (roundPrec c.rounding neg co e c.prec).2).toNat)
        (foldExp c (roundPrec c.rounding neg co e c.prec).2) ∧
      (Signal.inexact ∈ fl' ↔ Signal.inexact ∈ fl ∨ co % 10 ^ (numDigits co - c.prec) ≠ 0) ∧
      (Signal.rounded ∈ fl' ↔ Signal.rounded ∈ fl ∨ c.prec < numDigits co) := by
  by_cases hn : numDigits co ≤ c.prec
  · have hr : roundPrec c.rounding neg co e c.prec = (co, e) := by simp [roundPrec, hn]
    rw [hr] at hover ⊢
    have hk : numDigits co - c.prec = 0 := by omega
    rw [hk] at hmin ⊢
    obtain ⟨f1, f2, f3⟩ := fix_fits c neg co e fl fl' d hn hover (by simpa using hmin) hok
    refine ⟨f1, ?_, ?_⟩
    · rw [f2]
      simp [Nat.mod_one]
    · rw [f3]
      simp [Nat.not_lt.mpr hn]
  · have hp2 : c.prec < numDigits co := by omega
    have hkv : ((numDigits co - c.prec : Nat) : Int) = (numDigits co : Int) - c.prec := by omega
    obtain ⟨hlo, hhi⟩ := prefix_bounds co c.prec hc hp hp2
    -- the rounded coefficient has `prec` digits, so `hover` bounds its exponent by `Etop`
    have hfit : (roundPrec c.rounding neg co e c.prec).2 ≤ c.etop ∧
        numDigits (roundPrec c.rounding neg co e c.prec).1 = c.prec := by
      have hge := roundSpec_ge c.rounding neg (co / 10 ^ (numDigits co - c.prec))
        (co % 10 ^ (numDigits co - c.prec)) (10 ^ (numDigits co - c.prec))
      have hle := roundSpec_le c.rounding neg (co / 10 ^ (numDigits co - c.prec))
        (co % 10 ^ (numDigits co - c.prec)) (10 ^ (numDigits co - c.prec))
      have hdg : numDigits (roundPrec c.rounding neg co e c.prec).1 = c.prec := by
        simp only [roundPrec, hn, ↓reduceIte]
        split
        · have hpos : 10 ^ (c.prec - 1) < 10 ^ c.prec :=
            Nat.pow_lt_pow_right (by decide) (by omega)
          exact numDigits_eq (Nat.le_refl _) hpos hp
        · rename_i hne
          exact numDigits_eq (by omega) (by omega) hp
      rw [hdg] at hover
      refine ⟨?_, hdg⟩
      simp only [Ctx.etop]
      omega
    have hfold : foldExp c (roundPrec c.rounding neg co e c.prec).2 = (roundPrec c.rounding neg co e c.prec).2 := by
      unfold foldExp
      cases c.clamp
      · rfl
      · simp only [↓reduceIte]
        have := hfit.1
        omega
    have hexpMin : (numDigits co : Int) + e - c.prec ≤ (roundPrec c.rounding neg co e c.prec).2 := by
      simp only [roundPrec, hn, ↓reduceIte]
      split <;> simp only <;> omega
    simp only [fix] at hok
    have hc' : ¬ co = 0 := hc
    simp only [hc', ↓reduceIte] at hok
    rw [if_neg (by have := hfit.1; omega)] at hok
    have hsub : decide ((numDigits co : Int) + e - c.prec < c.etiny) = false := by
      simp only [decide_eq_false_iff_not]
      omega
    simp only [hsub, Bool.false_eq_true, ↓reduceIte] at hok
    rw [if_pos (by omega)] at hok
    obtain ⟨f1, f2, f3⟩ := fixRound_normal c neg co e fl fl' d hc hp hp2 hfit.1 hok
    rw [hfold]
    refine ⟨by rw [f1]; simp, f3, ?_⟩
    constructor
    · exact fun _ => Or.inr hp2
    · exact fun _ => f2

theorem mul_fin (c : Ctx) (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int)
    (fl fl' : List Signal) (d : Dec) (ha : ca ≠ 0) (hb : cb ≠ 0)
    (h : (mul c (.fin sa ca ea) (.fin sb cb eb)).run fl = .ok (d, fl')) :
    (fix c (.fin (sa != sb) (ca * cb) (ea + eb))).run fl = .ok (d, fl') := by
  have hm : mul c (.fin sa ca ea) (.fin sb cb eb) = mulFin c (sa != sb) ca ea cb eb := rfl
  rw [hm] at h
  simp only [mulFin, ha, hb, or_self, ↓reduceIte] at h
  by_cases h1 : ca = 1
  · subst h1
    simpa using h
  simp only [h1, ↓reduceIte] at h
  by_cases h2 : cb = 1
  · subst h2
    simpa using h
  simp only [h2, ↓reduceIte] at h
  obtain ⟨_, fl1, a1, a2⟩ := bind_ok h
  obtain ⟨_, rfl⟩ := liftPy_ok a1
  obtain ⟨_, fl2, a3, a4⟩ := bind_ok a2
  obtain ⟨_, rfl⟩ := liftPy_ok a3
  obtain ⟨_, fl3, a5, a6⟩ := bind_ok a4
  obtain ⟨_, rfl⟩ := liftPy_ok a5
  exact a6

/-- For every context (`prec ≥ 1`) and all finite non-zero operands, when `*`
returns a value in the normal range (no subnormal result, no overflow after
rounding), that value is the exact product correctly rounded to `prec` digits
in the context's rounding mode, Inexact is set exactly when non-zero digits were
dropped, and Rounded exactly when any digits were dropped. -/
def MulCorrect : Prop :=
  ∀ (c : Ctx) (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int)
    (fl fl' : List Signal) (d : Dec),
    1 ≤ c.prec → ca ≠ 0 → cb ≠ 0 →
    let P := ca * cb
    let e := ea + eb
    let neg := sa != sb
    let r := roundPrec c.rounding neg P e c.prec
    c.etiny ≤ e + (numDigits P - c.prec : Nat) →
    r.2 + numDigits r.1 - 1 ≤ c.emax →
    (mul c (.fin sa ca ea) (.fin sb cb eb)).run fl = .ok (d, fl') →
    d = .fin neg (r.1 * 10 ^ (r.2 - foldExp c r.2).toNat) (foldExp c r.2) ∧
    (Signal.inexact ∈ fl' ↔ Signal.inexact ∈ fl ∨ P % 10 ^ (numDigits P - c.prec) ≠ 0) ∧
    (Signal.rounded ∈ fl' ↔ Signal.rounded ∈ fl ∨ c.prec < numDigits P)

theorem mulCorrect_proven : MulCorrect := by
  intro c sa ca ea sb cb eb fl fl' d hp ha hb P e neg r hmin hover h
  exact fix_normal c neg P e fl fl' d (Nat.mul_ne_zero ha hb) hp hmin hover (mul_fin c sa ca ea sb cb eb fl fl' d ha hb h)

end PyLean.Decimal
