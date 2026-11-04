import PyLean.Decimal.Exact3
import PyLean.Decimal.Quantize

/-!
`quantize` stated outright, for every operand pair: the earlier `QuantizeCorrect` held only when
`quantize` returns.
-/

namespace PyLean.Decimal

open PyLean

/-- Signal `ss` in order, the first trapped one raising (`_raise_error`, _pydecimal.py:4105-4125),
then go on with the flags set. -/
def sigThen {β : Type} (c : Ctx) : List Signal → List Signal → (List Signal → Py β) → Py β
  | [], fl, k => k fl
  | s :: ss, fl, k => if s ∈ c.traps then .error (.named s.name "~") else sigThen c ss (addFlag s fl) k

/-- `quantize(a, q, rounding)` (_pydecimal.py:2600-2659) for every context and rounding argument
`m` (the context's when not given), on every operand pair. For finite `±co·10^e` and a finite
target with exponent `qe`, with `v` the coefficient `quantSpec` gives (`co` padded with zeros when
`qe ≤ e`, otherwise `co` with its last `qe - e` digits dropped and rounded as `m` says):

* a target exponent outside `[Etiny, Emax]` is InvalidOperation (:2626-2629);
* a zero becomes the zero of its sign at `qe` through `_fix` (:2632-2634);
* the operand's adjusted exponent above `Emax`, or `adjusted - qe + 1` above `prec`, is
  InvalidOperation (:2636-2643);
* `_rescale` raises the int/str-limit `ValueError` when the rounding incremented a coefficient
  of more than 4300 digits (`str(int(coeff) + 1)`);
* otherwise a result whose adjusted exponent exceeds `Emax` or which has more than `prec` digits is
  InvalidOperation (:2645-2650); else Subnormal (a non-zero result below `Emin`), Inexact (when
  non-zero digits were dropped) and Rounded (when any were) are signalled in that order, the first
  trapped one raising, and the result `±v·10^qe` goes through `_fix` (:2651-2659).

A NaN operand goes through `_check_nans` (:2612-2614); two infinities give the first operand
(:2616-2618); one infinity is InvalidOperation (:2620-2621). -/
def QuantizeExact : Prop :=
  ∀ (c : Ctx) (r : Option Rounding) (fl : List Signal),
    (∀ (neg : Bool) (co : Nat) (e : Int) (qn : Bool) (qc : Nat) (qe : Int),
      let v := quantSpec (r.getD c.rounding) neg co e qe
      let K := (qe - e).toNat
      (¬(c.etiny ≤ qe ∧ qe ≤ c.emax) →
        (quantize c (.fin neg co e) (.fin qn qc qe) r).run fl =
          afterSig c .invalidOperation fl (.nan false false 0)) ∧
      (c.etiny ≤ qe ∧ qe ≤ c.emax → co = 0 →
        (quantize c (.fin neg co e) (.fin qn qc qe) r).run fl = (fix c (.fin neg 0 qe)).run fl) ∧
      (c.etiny ≤ qe ∧ qe ≤ c.emax → co ≠ 0 →
        (c.emax < adjustedD co e ∨ (c.prec : Int) < adjustedD co e - qe + 1) →
        (quantize c (.fin neg co e) (.fin qn qc qe) r).run fl =
          afterSig c .invalidOperation fl (.nan false false 0)) ∧
      (c.etiny ≤ qe ∧ qe ≤ c.emax → co ≠ 0 → adjustedD co e ≤ c.emax →
        adjustedD co e - qe + 1 ≤ (c.prec : Int) →
        e < qe → v ≠ co / 10 ^ K → maxStrDigits < numDigits v →
        ∃ msg, (quantize c (.fin neg co e) (.fin qn qc qe) r).run fl = .error (.valueError msg)) ∧
      (c.etiny ≤ qe ∧ qe ≤ c.emax → co ≠ 0 → adjustedD co e ≤ c.emax →
        adjustedD co e - qe + 1 ≤ (c.prec : Int) →
        (qe ≤ e ∨ v = co / 10 ^ K ∨ numDigits v ≤ maxStrDigits) →
        (quantize c (.fin neg co e) (.fin qn qc qe) r).run fl =
          if c.emax < qe + numDigits v - 1 ∨ c.prec < numDigits v then
            afterSig c .invalidOperation fl (.nan false false 0)
          else sigThen c
            ((if v ≠ 0 ∧ qe + numDigits v - 1 < c.emin then [.subnormal] else []) ++
              (if e < qe then (if co % 10 ^ K ≠ 0 then [.inexact] else []) ++ [.rounded] else []))
            fl (fun fl' => (fix c (.fin neg v qe)).run fl'))) ∧
    (∀ a q : Dec, nanKind a ≠ 0 ∨ nanKind q ≠ 0 → (quantize c a q r).run fl = nanSpec2 c a q fl) ∧
    (∀ na nb : Bool, (quantize c (.inf na) (.inf nb) r).run fl = .ok (.inf na, fl)) ∧
    (∀ (na qn : Bool) (qc : Nat) (qe : Int),
      (quantize c (.inf na) (.fin qn qc qe) r).run fl = afterSig c .invalidOperation fl (.nan false false 0) ∧
      (quantize c (.fin qn qc qe) (.inf na) r).run fl = afterSig c .invalidOperation fl (.nan false false 0))

theorem quantizeFin_run (c : Ctx) (m : Rounding) (neg : Bool) (co : Nat) (e qe : Int) (qn : Bool)
    (qc : Nat) (r : Option Rounding) (hm : r.getD c.rounding = m) :
    quantize c (.fin neg co e) (.fin qn qc qe) r = quantizeFin c m neg co e qe := by
  subst hm; rfl

theorem quantizeExact_proven : QuantizeExact := by
  intro c r fl
  refine ⟨fun neg co e qn qc qe => ?_, fun a q h => ?_, fun na nb => ?_, fun na qn qc qe => ?_⟩
  · intro v K
    have hrun := quantizeFin_run c (r.getD c.rounding) neg co e qe qn qc r rfl
    refine ⟨fun h => ?_, fun h hc => ?_, fun h hc hb => ?_, fun h hc h1 h2 he hv hl => ?_,
      fun h hc h1 h2 hok => ?_⟩
    · rw [hrun]
      simp only [quantizeFin, if_pos h]
      (try rw [bind_pure]); exact invalid_run c fl
    · rw [hrun]
      simp only [quantizeFin, h, and_self, not_true_eq_false, ↓reduceIte, hc]
      try rw [bind_pure]
    · rw [hrun]
      simp only [quantizeFin, h, and_self, not_true_eq_false, ↓reduceIte, hc]
      rcases hb with hb | hb
      · simp only [show adjustedD co e > c.emax from hb, ↓reduceIte]
        (try rw [bind_pure]); exact invalid_run c fl
      · by_cases ha : adjustedD co e > c.emax
        · simp only [ha, ↓reduceIte]
          (try rw [bind_pure]); exact invalid_run c fl
        · simp only [ha, ↓reduceIte, show adjustedD co e - qe + 1 > c.prec from hb]
          (try rw [bind_pure]); exact invalid_run c fl
    · obtain ⟨msg, hm⟩ := (rescale_exact (r.getD c.rounding) neg co e qe hc he).2
        (by simpa [v, quantSpec, show ¬ e ≥ qe by omega] using hv)
        (by simpa [v, quantSpec, show ¬ e ≥ qe by omega] using hl)
      refine ⟨msg, ?_⟩
      rw [hrun]
      simp only [quantizeFin, h, and_self, not_true_eq_false, ↓reduceIte, hc,
        show ¬ adjustedD co e > c.emax by omega, show ¬ adjustedD co e - qe + 1 > c.prec by omega]
      rw [liftPy_run, hm]
    · have hres : rescale (.fin neg co e) qe (r.getD c.rounding) = .ok (.fin neg v qe) := by
        by_cases he : e < qe
        · have hv : quantSpec (r.getD c.rounding) neg co e qe =
              roundSpec (r.getD c.rounding) neg (co / 10 ^ (qe - e).toNat) (co % 10 ^ (qe - e).toNat)
                (10 ^ (qe - e).toNat) := by
            simp only [quantSpec, show ¬ e ≥ qe by omega, ↓reduceIte]
          have hv' : v = roundSpec (r.getD c.rounding) neg (co / 10 ^ (qe - e).toNat)
              (co % 10 ^ (qe - e).toNat) (10 ^ (qe - e).toNat) := hv
          rw [hv']
          refine (rescale_exact (r.getD c.rounding) neg co e qe hc he).1 ?_
          rcases hok with hok | hok | hok
          · omega
          · left; have := hok; rw [hv'] at this; exact this
          · right; have := hok; rw [hv'] at this; exact this
        · simp only [rescale, hc, ↓reduceIte, show e ≥ qe by omega, v, quantSpec]
      rw [hrun]
      simp only [quantizeFin, h, and_self, not_true_eq_false, ↓reduceIte, hc,
        show ¬ adjustedD co e > c.emax by omega, show ¬ adjustedD co e - qe + 1 > c.prec by omega]
      rw [liftPy_run, hres]
      simp only [adjustedD]
      by_cases hA : c.emax < qe + numDigits v - 1
      · simp only [show qe + (numDigits v : Int) - 1 > c.emax from hA, ↓reduceIte, true_or]
        (try rw [bind_pure]); exact invalid_run c fl
      by_cases hB : c.prec < numDigits v
      · simp only [show ¬ qe + (numDigits v : Int) - 1 > c.emax by omega, show numDigits v > c.prec from hB,
          ↓reduceIte, or_true]
        (try rw [bind_pure]); exact invalid_run c fl
      simp only [show ¬ qe + (numDigits v : Int) - 1 > c.emax by omega, show ¬ numDigits v > c.prec by omega,
        ↓reduceIte, hA, hB, or_self]
      have heq : e < qe → (cmpVal (.fin neg v qe) (.fin neg co e) = .eq ↔ co % 10 ^ K = 0) :=
        fun he => cmpVal_quantized (r.getD c.rounding) neg co e qe hc he
      by_cases hS : v ≠ 0 ∧ qe + (numDigits v : Int) - 1 < c.emin
      · simp only [hS, ne_eq, not_false_eq_true, and_self, ↓reduceIte, List.cons_append, List.nil_append]
        rw [raiseSig_bind]
        simp only [sigThen]
        split
        · rfl
        · simp only [quantizeFlags]
          by_cases he : e < qe
          · have heq' := heq he
            simp only [show qe > e from he, ↓reduceIte, he]
            by_cases hI : co % 10 ^ K = 0
            · simp only [show ¬ cmpVal (.fin neg v qe) (.fin neg co e) ≠ .eq by simpa using heq'.mpr hI,
                ↓reduceIte, hI, ne_eq, not_true_eq_false, List.nil_append, sigThen]
              (try rw [pure_bind]); rw [raiseSig_bind]
            · simp only [show cmpVal (.fin neg v qe) (.fin neg co e) ≠ .eq from fun h0 => hI (heq'.mp h0),
                ↓reduceIte, hI, ne_eq, not_false_eq_true, List.cons_append, List.nil_append, sigThen]
              rw [raiseSig_bind]
              split
              · rfl
              · rw [raiseSig_bind]
          · simp only [show ¬ qe > e by omega, ↓reduceIte, he, List.append_nil, sigThen]
            try rw [pure_bind]
      · simp only [hS, ↓reduceIte, List.nil_append]
        try rw [pure_bind]
        simp only [quantizeFlags]
        by_cases he : e < qe
        · have heq' := heq he
          simp only [show qe > e from he, ↓reduceIte, he]
          by_cases hI : co % 10 ^ K = 0
          · simp only [show ¬ cmpVal (.fin neg v qe) (.fin neg co e) ≠ .eq by simpa using heq'.mpr hI,
              ↓reduceIte, hI, ne_eq, not_true_eq_false, List.nil_append, sigThen]
            (try rw [pure_bind]); rw [raiseSig_bind]
          · simp only [show cmpVal (.fin neg v qe) (.fin neg co e) ≠ .eq from fun h0 => hI (heq'.mp h0),
              ↓reduceIte, hI, ne_eq, not_false_eq_true, List.cons_append, List.nil_append, sigThen]
            rw [raiseSig_bind]
            split
            · rfl
            · rw [raiseSig_bind]
        · simp only [show ¬ qe > e by omega, ↓reduceIte, he, sigThen]
          try rw [pure_bind]
  · rcases a with ⟨_, _, _⟩ | _ | ⟨_, sa, _⟩ <;> rcases q with ⟨_, _, _⟩ | _ | ⟨_, sq, _⟩ <;>
      first
      | (simp [nanKind] at h; done)
      | (simp only [quantize]; exact checkNans_return c _ _ fl _ (fun d => rfl) h)
  · simp [quantize, checkNans]; rfl
  · refine ⟨?_, ?_⟩
    · simp only [quantize, checkNans]
      rw [pure_bind]; exact invalid_run c fl
    · simp only [quantize, checkNans]
      rw [pure_bind]; exact invalid_run c fl

end PyLean.Decimal
