import PyLean.Decimal.MulProps
import PyLean.Decimal.CmpProps
import PyLean.Decimal.Props

/-!
`_fix` over its whole domain: the correctly rounded value of every finite decimal in every
context, overflow and the subnormal range included, with the signals in the order the source
raises them and the first trapped one raising.
-/

namespace PyLean.Decimal

open PyLean

/-- Signal `ss` in order, then return `v`: the first trapped signal raises its exception, every
other one is flagged. -/
def sigRun (c : Ctx) : List Signal → List Signal → Dec → Py (Dec × List Signal)
  | [], fl, v => .ok (v, fl)
  | s :: ss, fl, v => if s ∈ c.traps then .error (.named s.name "~") else sigRun c ss (addFlag s fl) v

theorem raiseSig_bind {β : Type} (c : Ctx) (s : Signal) (k : Unit → DM β) (fl : List Signal) :
    (raiseSig c s >>= k).run fl =
      if s ∈ c.traps then .error (.named s.name "~") else (k ()).run (addFlag s fl) := by
  unfold addFlag
  by_cases h : s ∈ c.traps <;>
    simp [raiseSig, h, StateT.run, bind, StateT.bind, Except.bind, modify, modifyGet,
      MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw, StateT.lift, Except.tryCatch]

theorem pure_run {β : Type} (v : β) (fl : List Signal) : (pure v : DM β).run fl = .ok (v, fl) := rfl

theorem sigRun_cons (c : Ctx) (s : Signal) (ss : List Signal) (fl : List Signal) (v : Dec) :
    sigRun c (s :: ss) fl v =
      if s ∈ c.traps then .error (.named s.name "~") else sigRun c ss (addFlag s fl) v := rfl

/-- The exact value `±co·10^e` rounded into the context, as the specification describes it
(General Decimal Arithmetic, "Rounding" and "Exceptional conditions"; decimal docs, "Signals"):

* an adjusted exponent above `Emax` overflows: `Overflow`, `Inexact`, `Rounded`, and the
  overflow value of the rounding mode;
* otherwise the result's exponent is `emn = max(e + digits - prec, Etiny)`; a value whose
  exponent is already at least `emn` is kept (folded down to `Etop` under `clamp=1`, which
  signals `Clamped`), signalling `Subnormal` when its adjusted exponent is below `Emin`;
* otherwise the digits below `10^emn` are dropped as the rounding mode says (`roundSpec`), a
  carry to `10^prec` takes one more exponent, a result above `Etop` overflows, and the signals
  are `Overflow`, `Underflow` (inexact and subnormal), `Subnormal`, `Inexact` (non-zero digits
  dropped), `Rounded`, and `Clamped` for a zero result.

`_pydecimal` adds one outcome of its own: the int/str-limit `ValueError` when the rounded
coefficient is the kept prefix plus one and has more than 4300 digits (`str(int(coeff)+1)`,
_pydecimal.py:1767). -/
def fixSpec (c : Ctx) (neg : Bool) (co : Nat) (e : Int) (fl : List Signal) : Py (Dec × List Signal) :=
  let nd : Int := numDigits co
  if e + nd - 1 > c.emax then sigRun c [.overflow, .inexact, .rounded] fl (overflowResult c neg)
  else
    let sub := decide (nd + e - c.prec < (c.emin - c.prec + 1))
    let emn := max (nd + e - c.prec) (c.emin - c.prec + 1)
    let subs : List Signal := if sub then [.subnormal] else []
    if emn ≤ e then
      if c.clamp ∧ e > (c.emax - c.prec + 1) then
        sigRun c (subs ++ [.clamped]) fl (.fin neg (co * 10 ^ (e - (c.emax - c.prec + 1)).toNat) (c.emax - c.prec + 1))
      else sigRun c subs fl (.fin neg co e)
    else
      let k := (emn - e).toNat
      let q := co / 10 ^ k
      let r := co % 10 ^ k
      let q' := roundSpec c.rounding neg q r (10 ^ k)
      let dg := (nd + e - emn).toNat
      if q' ≠ q ∧ maxStrDigits < numDigits q' then
        .error (.valueError (if dg > maxStrDigits then limitToIntMsg dg else limitToStrMsg))
      else
        let cf := if numDigits q' > c.prec then q' / 10 else q'
        let ef := if numDigits q' > c.prec then emn + 1 else emn
        let over := decide (ef > (c.emax - c.prec + 1))
        let v := if over then overflowResult c neg else Dec.fin neg cf ef
        sigRun c ((if over then [.overflow] else []) ++ (if r ≠ 0 ∧ sub then [.underflow] else []) ++
          subs ++ (if r ≠ 0 then [.inexact] else []) ++ [.rounded] ++
          (if isZero v then [.clamped] else [])) fl v

theorem ite_unit_run {β : Type} (b : Prop) [Decidable b] (c : Ctx) (s : Signal) (k : Unit → DM β)
    (fl : List Signal) :
    ((if b then raiseSig c s else (pure () : DM Unit)) >>= k).run fl =
      if b then (if s ∈ c.traps then .error (.named s.name "~") else (k ()).run (addFlag s fl))
      else (k ()).run fl := by
  by_cases hb : b
  · simp only [hb, ↓reduceIte, raiseSig_bind]
  · simp only [hb, ↓reduceIte]; rfl

/-- The signalling tail of `_fix`'s rounding branch, _pydecimal.py:1773-1791. -/
theorem fixFinish_run (c : Ctx) (neg : Bool) (cf : Nat) (ef : Int) (ch : Int) (sub : Bool)
    (fl : List Signal) :
    (fixFinish c neg cf ef ch sub).run fl =
      let over := decide (ef > c.etop)
      let v := if over then overflowResult c neg else Dec.fin neg cf ef
      sigRun c ((if over then [.overflow] else []) ++ (if ch ≠ 0 ∧ sub then [.underflow] else []) ++
          (if sub then [.subnormal] else []) ++ (if ch ≠ 0 then [.inexact] else []) ++ [.rounded] ++
          (if isZero v then [.clamped] else [])) fl v := by
  simp only [fixFinish]
  by_cases ho : ef > c.etop <;>
  by_cases h1 : ch = 0 <;> cases sub <;>
  by_cases hz : isZero (if decide (ef > c.etop) = true then overflowResult c neg else Dec.fin neg cf ef) = true <;>
  simp only [ho, h1, decide_true, decide_false, ↓reduceIte, raiseSig_bind, pure_run, ite_unit_run,
    bind_assoc, pure_bind, Bool.false_eq_true, and_true, and_false, not_true_eq_false, ne_eq,
    not_false_eq_true, List.nil_append, List.cons_append, sigRun_cons, sigRun] at hz ⊢ <;>
  simp only [hz, ↓reduceIte, raiseSig_bind, pure_run, sigRun_cons, sigRun, Bool.false_eq_true]

theorem incr_run (q D : Nat) (hD : 1 ≤ D → 10 ^ (D - 1) ≤ q) :
    incr q D = if maxStrDigits < numDigits (q + 1) then
      .error (.valueError (if D > maxStrDigits then limitToIntMsg D else limitToStrMsg))
      else .ok (q + 1) := by
  by_cases h : maxStrDigits < numDigits (q + 1)
  · simp only [h, ↓reduceIte]
    by_cases hd : D > maxStrDigits
    · have : max D 1 = D := by simp only [maxStrDigits] at hd; omega
      simp [incr, intLimit, hd, this, bind, Except.bind, show max D 1 > maxStrDigits by omega]
    · have : ¬ max D 1 > maxStrDigits := by simp only [maxStrDigits] at hd ⊢; omega
      simp [incr, intLimit, strLimit, this, hd, h, bind, Except.bind]
  · simp only [h, ↓reduceIte]
    exact (incr_exact q D hD).1 (by omega)

/-- The carry of `_fix`, _pydecimal.py:1766-1771. -/
theorem fixCarry_run {β : Type} (c : Ctx) (q : Nat) (ch : Int) (D : Nat) (emn : Int)
    (k : Nat × Int → DM β) (fl : List Signal) (hD : 1 ≤ D → 10 ^ (D - 1) ≤ q)
    (hch : ch = 1 ∨ ch = 0 ∨ ch = -1) :
    (fixCarry c q ch D emn >>= k).run fl =
      if ch = 1 then
        (if maxStrDigits < numDigits (q + 1) then
          .error (.valueError (if D > maxStrDigits then limitToIntMsg D else limitToStrMsg))
        else (k (if numDigits (q + 1) > c.prec then ((q + 1) / 10, emn + 1) else (q + 1, emn))).run fl)
      else (k (q, emn)).run fl := by
  have hi := incr_run q D hD
  rcases hch with rfl | rfl | rfl
  · simp only [fixCarry, show (1 : Int) > 0 by decide, ↓reduceIte, liftPy, hi]
    by_cases h : maxStrDigits < numDigits (q + 1)
    · simp [h, liftPy, StateT.run, bind, StateT.bind, Except.bind, Functor.map, Except.map]
    · by_cases h2 : numDigits (q + 1) > c.prec <;>
        simp [h, h2, liftPy, StateT.run, bind, StateT.bind, Except.bind, Functor.map, Except.map, pure,
          StateT.pure, Except.pure]
  · simp [fixCarry]
  · simp [fixCarry]

/-- The digit count and the rounding direction `_fix` computes, _pydecimal.py:1760-1765:
`k` digits are dropped and `D` kept. -/
theorem fixDigits_round (m : Rounding) (neg : Bool) (co : Nat) (e emn : Int) (hc : co ≠ 0)
    (he : e < emn) :
    (fixDigits co e emn).2 = ((numDigits co : Int) + e - emn).toNat ∧
    roundKeep m neg (fixDigits co e emn).1 (fixDigits co e emn).2 =
      (co / 10 ^ (emn - e).toNat, roundDir m neg (co / 10 ^ (emn - e).toNat) (co % 10 ^ (emn - e).toNat)
        (5 * 10 ^ ((emn - e).toNat - 1))) ∧
    (1 ≤ ((numDigits co : Int) + e - emn).toNat →
      10 ^ (((numDigits co : Int) + e - emn).toNat - 1) ≤ co / 10 ^ (emn - e).toNat) ∧
    co / 10 ^ (emn - e).toNat < 10 ^ ((numDigits co : Int) + e - emn).toNat := by
  have hcl : co < 10 ^ (numDigits co) := lt_pow_numDigits co
  unfold fixDigits
  by_cases hd : (numDigits co : Int) + e - emn < 0
  · have hlt : numDigits co < (emn - e).toNat := by omega
    have hK : 10 ^ (numDigits co) ≤ 10 ^ (emn - e).toNat := Nat.pow_le_pow_right (by decide) (by omega)
    have hc2 : co < 5 * 10 ^ ((emn - e).toNat - 1) := by
      have : 10 ^ (numDigits co) ≤ 10 ^ ((emn - e).toNat - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have hq : co / 10 ^ (emn - e).toNat = 0 := Nat.div_eq_of_lt (by omega)
    have hrr : co % 10 ^ (emn - e).toNat = co := Nat.mod_eq_of_lt (by omega)
    have hsm := roundDir_small m neg co _ hc
      (by have : 1 ≤ 10 ^ ((emn - e).toNat - 1) := Nat.one_le_pow _ _ (by decide); omega) hc2
    have hD : ((numDigits co : Int) + e - emn).toNat = 0 := by omega
    simp only [hd, ↓reduceIte, roundKeep, hq, hrr, hD]
    refine ⟨trivial, ?_, fun h => absurd h (by decide), by decide⟩
    rw [← hsm]
    rfl
  · have hdg : numDigits co - ((numDigits co : Int) + e - emn).toNat = (emn - e).toNat := by omega
    simp only [hd, ↓reduceIte, roundKeep, hdg]
    refine ⟨trivial, trivial, fun h1 => ?_, ?_⟩
    · have hl := pow_numDigits_le hc
      rw [Nat.le_div_iff_mul_le (Nat.pow_pos (by decide)), ← Nat.pow_add]
      exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hl
    · rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide)), ← Nat.pow_add]
      exact Nat.lt_of_lt_of_le hcl (Nat.pow_le_pow_right (by decide) (by omega))

theorem fixExact_fin (c : Ctx) (neg : Bool) (co : Nat) (e : Int) (fl : List Signal)
    (hp : 1 ≤ c.prec) (hc : co ≠ 0) :
    (fix c (.fin neg co e)).run fl = fixSpec c neg co e fl := by
  have ht : c.etiny = c.emin - c.prec + 1 := rfl
  have ht' : c.etop = c.emax - c.prec + 1 := rfl
  unfold fix fixSpec
  simp only [hc, ↓reduceIte]
  rw [← ht, ← ht']
  by_cases hov : e + (numDigits co : Int) - 1 > c.emax
  · have h1 : (numDigits co : Int) + e - c.prec > c.etop := by simp only [Ctx.etop]; omega
    simp only [h1, hov, ↓reduceIte, raiseSig_bind, pure_run, sigRun_cons, sigRun]
  have h1 : ¬ ((numDigits co : Int) + e - c.prec > c.etop) := by simp only [Ctx.etop]; omega
  simp only [h1, hov, ↓reduceIte]
  have hemn : (if decide ((numDigits co : Int) + e - c.prec < c.etiny) = true then c.etiny
      else (numDigits co : Int) + e - c.prec) = max ((numDigits co : Int) + e - c.prec) c.etiny := by
    split <;> simp_all <;> omega
  rw [hemn]
  generalize hE : max ((numDigits co : Int) + e - c.prec) c.etiny = emn at *
  generalize hS : decide ((numDigits co : Int) + e - c.prec < c.etiny) = sub at *
  by_cases hr : e < emn
  · have hnr : ¬ emn ≤ e := by omega
    simp only [hr, hnr, ↓reduceIte, fixRound]
    obtain ⟨hD2, hRK, hD, hqlt⟩ := fixDigits_round c.rounding neg co e emn hc hr
    rw [hRK, hD2]
    generalize hK : (emn - e).toNat = K at *
    have hK1 : 1 ≤ K := by omega
    have hb := pow_ten_eq_two_half hK1
    have hrlt : co % 10 ^ K < 10 ^ K := Nat.mod_lt _ (Nat.pow_pos (by decide))
    generalize hD' : ((numDigits co : Int) + e - emn).toNat = D at *
    have hDp : D ≤ c.prec := by omega
    generalize hq : co / 10 ^ K = q at *
    generalize hrm : co % 10 ^ K = rem at *
    have hsp := roundDir_spec c.rounding neg q rem (5 * 10 ^ (K - 1)) (by omega)
    rw [← hb] at hsp
    generalize hdir : roundDir c.rounding neg q rem (5 * 10 ^ (K - 1)) = dir at *
    have hcases : dir = 1 ∨ dir = 0 ∨ dir = -1 := by
      have := roundDir_cases c.rounding neg q rem (5 * 10 ^ (K - 1)); rw [hdir] at this; exact this
    rw [fixCarry_run c q dir D emn (fun t => fixFinish c neg t.1 t.2 dir sub) fl hD hcases]
    have hz : (dir ≠ 0) = (rem ≠ 0) := by simp [hsp.2]
    by_cases h1 : dir = 1
    · have hq' : roundSpec c.rounding neg q rem (10 ^ K) = q + 1 := by
        rw [← hsp.1]; simp [h1]
      rw [hq']
      simp only [h1, ↓reduceIte, show q + 1 ≠ q by omega, ne_eq, not_false_eq_true, true_and]
      by_cases hl : maxStrDigits < numDigits (q + 1)
      · simp only [hl, ↓reduceIte]
      · simp only [hl, ↓reduceIte]
        rw [fixFinish_run]
        have hr0 : rem ≠ 0 := by intro h0; exact absurd (hsp.2.mpr h0) (by omega)
        by_cases hpc : numDigits (q + 1) > c.prec <;> simp [hpc, hr0]
    · have hq' : roundSpec c.rounding neg q rem (10 ^ K) = q := by
        rw [← hsp.1]; simp [h1]
      have hnq : ¬ numDigits q > c.prec := by
        by_cases hD0 : D = 0
        · subst hD0
          have : q = 0 := by simp at hqlt; omega
          subst this; rw [numDigits_zero]; omega
        · have := (numDigits_le_iff (show 0 < D by omega)).mpr hqlt
          omega
      rw [hq']
      simp only [h1, ↓reduceIte, ne_eq, not_true_eq_false, false_and, hnq]
      rw [fixFinish_run]
      simp only [hz]
  · have hr' : emn ≤ e := by omega
    simp only [hr, hr', ↓reduceIte, decide_true, decide_false]
    cases sub <;> by_cases hcl : c.clamp = true ∧ e > c.etop <;>
      simp only [hcl, ↓reduceIte, ite_unit_run, raiseSig_bind, pure_run, sigRun_cons, sigRun,
        Bool.false_eq_true, List.nil_append, List.cons_append, bind_assoc, pure_bind, and_self,
        and_true, true_and, and_false, false_and]

/-- `_fix(context)` (_pydecimal.py:1713-1803) for every context with `prec ≥ 1`: a finite
non-zero value is `fixSpec` (correct rounding into `[Etiny, Etop]` with `Etiny = Emin - prec + 1`
and `Etop = Emax - prec + 1`, overflow, the subnormal range, the clamp fold-down, the signals in
the order of the specification and the first trapped one raising, and `_pydecimal`'s int-limit
`ValueError`); a zero keeps its sign and has its exponent clamped into `[Etiny, Emax]`
(`[Etiny, Etop]` under `clamp=1`), signalling `Clamped` when that changes it; an infinity is
unchanged and a NaN keeps the last `prec - clamp` digits of its payload. -/
def FixExact : Prop :=
  ∀ (c : Ctx) (fl : List Signal), 1 ≤ c.prec →
    (∀ (neg : Bool) (co : Nat) (e : Int), co ≠ 0 → (fix c (.fin neg co e)).run fl = fixSpec c neg co e fl) ∧
    (∀ (neg : Bool) (e : Int),
      let ne := min (max e (c.emin - c.prec + 1)) (if c.clamp then c.emax - c.prec + 1 else c.emax)
      (fix c (.fin neg 0 e)).run fl =
        if ne ≠ e then sigRun c [.clamped] fl (.fin neg 0 ne) else .ok (.fin neg 0 e, fl)) ∧
    (∀ neg : Bool, (fix c (.inf neg)).run fl = .ok (.inf neg, fl)) ∧
    (∀ (neg s : Bool) (p : Nat), (fix c (.nan neg s p)).run fl = .ok (.nan neg s (p % 10 ^ nanDigits c), fl))

theorem fixExact_proven : FixExact := by
  intro c fl hp
  refine ⟨fun neg co e hc => fixExact_fin c neg co e fl hp hc, fun neg e => ?_, fun neg => rfl,
    fun neg s p => by simp [fix, fixNan_spec]; rfl⟩
  intro ne
  have ht : c.etiny = c.emin - c.prec + 1 := rfl
  have ht' : c.etop = c.emax - c.prec + 1 := rfl
  simp only [fix, ↓reduceIte]
  rw [ht, ht']
  by_cases h : ne = e
  · have h2 := h
    simp only [ne] at h
    simp only [h, h2, ↓reduceIte, ne_eq, not_true_eq_false]; rfl
  · simp only [ne] at h
    simp only [h, ↓reduceIte, ne_eq, not_false_eq_true, raiseSig_bind, pure_run, sigRun_cons, sigRun, ne]

end PyLean.Decimal
