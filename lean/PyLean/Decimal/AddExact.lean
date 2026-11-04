import PyLean.Decimal.Exact4
import PyLean.Decimal.OpenProps

/-!
`__add__` and `__sub__` over all finite operands: the exact sum rounded into the context by
`_fix` (`fixSpec`, overflow and the subnormal range included), plus `_pydecimal`'s int/str-limit
`ValueError`s, exactly where they are raised.

The heart is `_normalize`'s substitution (_pydecimal.py:5737-5744): an operand below
`10^exp`, `exp = min(tmp.exp - 1, tmp.adjusted() - prec - 1)`, is replaced by `1·10^exp`. The
working sum then has at least `prec + 1` digits, so `_fix` drops its last digit, and the sum and
the exact sum agree on every digit `_fix` keeps, on whether the dropped digits are zero (they are
not) and on how they compare with half a unit (`fixSpec_sticky`).
-/

namespace PyLean.Decimal

open PyLean

/-! ## `_fix` past `prec` digits, as a function of what it reads -/

/-- `fixSpec`'s rounding branch, written over `ae` (the digit count plus the exponent), the kept
prefix `q`, whether the dropped digits are non-zero (`rnz`), and the rounded prefix `q'`. -/
def fixR (c : Ctx) (neg : Bool) (ae : Int) (q : Nat) (rnz : Bool) (q' : Nat) (fl : List Signal) :
    Py (Dec × List Signal) :=
  if ae - 1 > c.emax then sigRun c [.overflow, .inexact, .rounded] fl (overflowResult c neg)
  else
    let sub := decide (ae - c.prec < (c.emin - c.prec + 1))
    let emn := max (ae - c.prec) (c.emin - c.prec + 1)
    let subs : List Signal := if sub then [.subnormal] else []
    let dg := (ae - emn).toNat
    if q' ≠ q ∧ maxStrDigits < numDigits q' then
      .error (.valueError (if dg > maxStrDigits then limitToIntMsg dg else limitToStrMsg))
    else
      let cf := if numDigits q' > c.prec then q' / 10 else q'
      let ef := if numDigits q' > c.prec then emn + 1 else emn
      let over := decide (ef > (c.emax - c.prec + 1))
      let v := if over then overflowResult c neg else Dec.fin neg cf ef
      sigRun c ((if over then [.overflow] else []) ++ (if rnz = true ∧ sub then [.underflow] else []) ++
        subs ++ (if rnz = true then [.inexact] else []) ++ [.rounded] ++
        (if isZero v then [.clamped] else [])) fl v

/-- The digits `fixSpec` drops from a coefficient of more than `prec` digits. -/
def fixK (c : Ctx) (co : Nat) (e : Int) : Nat :=
  (max ((numDigits co : Int) + e - c.prec) (c.emin - c.prec + 1) - e).toNat

theorem fixSpec_round (c : Ctx) (neg : Bool) (co : Nat) (e : Int) (fl : List Signal)
    (hp : c.prec < numDigits co) :
    fixSpec c neg co e fl =
      fixR c neg ((numDigits co : Int) + e) (co / 10 ^ fixK c co e) (decide (co % 10 ^ fixK c co e ≠ 0))
        (roundSpec c.rounding neg (co / 10 ^ fixK c co e) (co % 10 ^ fixK c co e) (10 ^ fixK c co e)) fl := by
  have hm := Int.le_max_left ((numDigits co : Int) + e - c.prec) (c.emin - c.prec + 1)
  have h2 : ¬ (max ((numDigits co : Int) + e - c.prec) (c.emin - c.prec + 1) ≤ e) := by omega
  have h1 : e + (numDigits co : Int) - 1 = (numDigits co : Int) + e - 1 := by omega
  unfold fixSpec fixR fixK
  simp only [h1, h2, ↓reduceIte, decide_eq_true_eq]

theorem roundSpec_congr (m : Rounding) (neg : Bool) (q r r' b b' : Nat) (hr : r ≠ 0) (hr' : r' ≠ 0)
    (h1 : 2 * r ≥ b ↔ 2 * r' ≥ b') (h2 : 2 * r > b ↔ 2 * r' > b') (h3 : 2 * r = b ↔ 2 * r' = b') :
    roundSpec m neg q r b = roundSpec m neg q r' b' := by
  cases m <;> simp only [roundSpec, hr, hr', h1, h2, h3, ne_eq, not_false_eq_true, true_and]

theorem divmod_of_eq (X B Q R : Nat) (h : X = B * Q + R) (hR : R < B) : X / B = Q ∧ X % B = R := by
  subst h
  have hB : 0 < B := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hR, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hR]

theorem pow_ten_eq_ten_mul {k : Nat} (hk : 1 ≤ k) : ∃ b1, 10 ^ k = 10 * b1 ∧ 0 < b1 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact ⟨10 ^ j, by rw [Nat.pow_succ'], Nat.pow_pos (by decide)⟩

/-- What the sticky digit keeps, for a sum: `W = A + 1` against `X = A·10^d + o` with `A` a multiple
of ten and `0 < o < 10^d`, written with `W ≡ 1 (mod 10)` and `X = (W - 1)·10^d + o`. Dropping
`k ≥ 1` digits of `W` and `k + d` of `X` keeps the same prefix, drops non-zero digits from both, and
the dropped part compares with half the same way (never equal to it). -/
theorem sticky_plus (W o d k : Nat) (hW : W % 10 = 1) (hk : 1 ≤ k) (ho0 : 0 < o)
    (ho : o < 10 ^ d) :
    ((W - 1) * 10 ^ d + o) / 10 ^ (k + d) = W / 10 ^ k ∧
    W % 10 ^ k ≠ 0 ∧ ((W - 1) * 10 ^ d + o) % 10 ^ (k + d) ≠ 0 ∧
    (2 * (W % 10 ^ k) ≥ 10 ^ k ↔ 2 * (((W - 1) * 10 ^ d + o) % 10 ^ (k + d)) ≥ 10 ^ (k + d)) ∧
    (2 * (W % 10 ^ k) > 10 ^ k ↔ 2 * (((W - 1) * 10 ^ d + o) % 10 ^ (k + d)) > 10 ^ (k + d)) ∧
    (2 * (W % 10 ^ k) = 10 ^ k ↔ 2 * (((W - 1) * 10 ^ d + o) % 10 ^ (k + d)) = 10 ^ (k + d)) := by
  obtain ⟨b1, hb, hb1⟩ := pow_ten_eq_ten_mul hk
  have hpow : 10 ^ (k + d) = 10 ^ k * 10 ^ d := Nat.pow_add 10 k d
  generalize hm : 10 ^ d = m at ho hpow ⊢
  generalize hBk : 10 ^ k = B at hb hpow ⊢
  rw [hpow]
  have hWQR : W = B * (W / B) + W % B := (Nat.div_add_mod W B).symm
  generalize hQ : W / B = Q at hWQR ⊢
  generalize hR : W % B = R at hWQR ⊢
  have hRlt : R < B := by rw [← hR]; exact Nat.mod_lt _ (by omega)
  have hR10 : R % 10 = 1 := by
    have h10 : 10 ∣ B := ⟨b1, hb⟩
    rw [← hR, Nat.mod_mod_of_dvd W h10, hW]
  have hBQ : B * Q = 10 * (b1 * Q) := by rw [hb, Nat.mul_assoc]
  obtain ⟨j, hj⟩ : ∃ j, R = 10 * j + 1 := ⟨R / 10, by omega⟩
  have hjb : j + 1 ≤ b1 := by omega
  have hW1 : W - 1 = B * Q + 10 * j := by omega
  have hX : (W - 1) * m + o = (B * m) * Q + (10 * (j * m) + o) := by
    rw [hW1, Nat.add_mul, Nat.mul_right_comm B Q m, Nat.mul_assoc 10 j m]; omega
  have hBm : B * m = 10 * (b1 * m) := by rw [hb, Nat.mul_assoc]
  have hjm : j * m + m ≤ b1 * m := by
    have := Nat.mul_le_mul_right m hjb
    rwa [Nat.add_mul, Nat.one_mul] at this
  have hlt : 10 * (j * m) + o < B * m := by omega
  obtain ⟨hdiv, hmod⟩ := divmod_of_eq _ _ _ _ hX hlt
  rw [hdiv, hmod]
  have hm1 : b1 ≤ 2 * j → b1 * m ≤ 2 * (j * m) := fun h => by
    have := Nat.mul_le_mul_right m h; rwa [Nat.mul_assoc] at this
  have hm2 : 2 * j + 1 ≤ b1 → 2 * (j * m) + m ≤ b1 * m := fun h => by
    have := Nat.mul_le_mul_right m h; rwa [Nat.add_mul, Nat.one_mul, Nat.mul_assoc] at this
  refine ⟨rfl, by omega, by omega, ?_, ?_, ?_⟩ <;>
  · by_cases h : b1 ≤ 2 * j
    · have := hm1 h; omega
    · have := hm2 (by omega); omega

/-- The sticky digit for a difference: `W = A - 1` against `X = A·10^d - o`, written with
`W ≡ 9 (mod 10)` and `X = (W + 1)·10^d - o`. -/
theorem sticky_minus (W o d k : Nat) (hW : W % 10 = 9) (hk : 1 ≤ k) (ho0 : 0 < o)
    (ho : o < 10 ^ d) :
    ((W + 1) * 10 ^ d - o) / 10 ^ (k + d) = W / 10 ^ k ∧
    W % 10 ^ k ≠ 0 ∧ ((W + 1) * 10 ^ d - o) % 10 ^ (k + d) ≠ 0 ∧
    (2 * (W % 10 ^ k) ≥ 10 ^ k ↔ 2 * (((W + 1) * 10 ^ d - o) % 10 ^ (k + d)) ≥ 10 ^ (k + d)) ∧
    (2 * (W % 10 ^ k) > 10 ^ k ↔ 2 * (((W + 1) * 10 ^ d - o) % 10 ^ (k + d)) > 10 ^ (k + d)) ∧
    (2 * (W % 10 ^ k) = 10 ^ k ↔ 2 * (((W + 1) * 10 ^ d - o) % 10 ^ (k + d)) = 10 ^ (k + d)) := by
  obtain ⟨b1, hb, hb1⟩ := pow_ten_eq_ten_mul hk
  have hpow : 10 ^ (k + d) = 10 ^ k * 10 ^ d := Nat.pow_add 10 k d
  generalize hm : 10 ^ d = m at ho hpow ⊢
  generalize hBk : 10 ^ k = B at hb hpow ⊢
  rw [hpow]
  have hWQR : W = B * (W / B) + W % B := (Nat.div_add_mod W B).symm
  generalize hQ : W / B = Q at hWQR ⊢
  generalize hR : W % B = R at hWQR ⊢
  have hRlt : R < B := by rw [← hR]; exact Nat.mod_lt _ (by omega)
  have hR10 : R % 10 = 9 := by
    have h10 : 10 ∣ B := ⟨b1, hb⟩
    rw [← hR, Nat.mod_mod_of_dvd W h10, hW]
  have hBQ : B * Q = 10 * (b1 * Q) := by rw [hb, Nat.mul_assoc]
  obtain ⟨j, hj⟩ : ∃ j, R = 10 * j + 9 := ⟨R / 10, by omega⟩
  have hjb : j + 1 ≤ b1 := by omega
  have hW1 : W + 1 = B * Q + 10 * (j + 1) := by omega
  have hum : (j + 1) * m = j * m + m := by rw [Nat.add_mul, Nat.one_mul]
  have hX : (W + 1) * m - o = (B * m) * Q + (10 * ((j + 1) * m) - o) := by
    rw [hW1, Nat.add_mul, Nat.mul_right_comm B Q m, Nat.mul_assoc 10 (j + 1) m]; omega
  have hBm : B * m = 10 * (b1 * m) := by rw [hb, Nat.mul_assoc]
  have hjm : j * m + m ≤ b1 * m := by
    have := Nat.mul_le_mul_right m hjb
    rwa [Nat.add_mul, Nat.one_mul] at this
  have hlt : 10 * ((j + 1) * m) - o < B * m := by omega
  obtain ⟨hdiv, hmod⟩ := divmod_of_eq _ _ _ _ hX hlt
  rw [hdiv, hmod]
  have hm1 : b1 ≤ 2 * j + 1 → b1 * m ≤ 2 * (j * m) + m := fun h => by
    have := Nat.mul_le_mul_right m h; rwa [Nat.add_mul, Nat.one_mul, Nat.mul_assoc] at this
  have hm2 : 2 * j + 2 ≤ b1 → 2 * (j * m) + 2 * m ≤ b1 * m := fun h => by
    have := Nat.mul_le_mul_right m h; rwa [Nat.add_mul, Nat.mul_assoc] at this
  refine ⟨rfl, by omega, by omega, ?_, ?_, ?_⟩ <;>
  · by_cases h : b1 ≤ 2 * j + 1
    · have := hm1 h; omega
    · have := hm2 (by omega); omega

theorem numDigits_bounds {W : Nat} (h : W ≠ 0) :
    10 ^ (numDigits W - 1) ≤ W ∧ W < 10 ^ numDigits W := ⟨pow_numDigits_le h, lt_pow_numDigits W⟩

theorem ten_le_numDigits {W : Nat} (h : 10 ≤ W) : 2 ≤ numDigits W := by
  have := lt_pow_numDigits W
  by_cases h1 : numDigits W ≤ 1
  · have h2 := (numDigits_le_iff (by decide : 0 < 1)).mp h1
    omega
  · omega

theorem pow_mod_ten {n : Nat} (h : 1 ≤ n) : 10 ^ n % 10 = 0 := by
  obtain ⟨b1, hb, _⟩ := pow_ten_eq_ten_mul h
  rw [hb]; simp

theorem numDigits_sticky_plus (W o d : Nat) (hW : W % 10 = 1) (h10 : 10 ≤ W) (ho : o < 10 ^ d) :
    numDigits ((W - 1) * 10 ^ d + o) = numDigits W + d := by
  have h2 := ten_le_numDigits h10
  obtain ⟨hl, hu⟩ := numDigits_bounds (show W ≠ 0 by omega)
  have hpm := pow_mod_ten (show 1 ≤ numDigits W - 1 by omega)
  have hne : 10 ^ (numDigits W - 1) ≤ W - 1 := by
    have : W ≠ 10 ^ (numDigits W - 1) := fun h => by rw [h] at hW; omega
    omega
  have hm0 : 0 < 10 ^ d := Nat.pow_pos (by decide)
  apply numDigits_eq
  · rw [show numDigits W + d - 1 = (numDigits W - 1) + d by omega, Nat.pow_add]
    have := Nat.mul_le_mul_right (10 ^ d) hne
    omega
  · rw [Nat.pow_add]
    have := Nat.mul_le_mul_right (10 ^ d) (show W - 1 + 1 ≤ 10 ^ numDigits W by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  · omega

theorem numDigits_sticky_minus (W o d : Nat) (h10 : 10 ≤ W) (ho0 : 0 < o) (ho : o < 10 ^ d) :
    numDigits ((W + 1) * 10 ^ d - o) = numDigits W + d := by
  have h2 := ten_le_numDigits h10
  obtain ⟨hl, hu⟩ := numDigits_bounds (show W ≠ 0 by omega)
  have hm0 : 0 < 10 ^ d := Nat.pow_pos (by decide)
  have hWm : (W + 1) * 10 ^ d = W * 10 ^ d + 10 ^ d := by rw [Nat.add_mul, Nat.one_mul]
  apply numDigits_eq
  · rw [show numDigits W + d - 1 = (numDigits W - 1) + d by omega, Nat.pow_add]
    have := Nat.mul_le_mul_right (10 ^ d) hl
    omega
  · rw [Nat.pow_add]
    have := Nat.mul_le_mul_right (10 ^ d) (show W + 1 ≤ 10 ^ numDigits W by omega)
    omega
  · omega

/-- The facts about the dropped digits `fixSpec_sticky` needs, at every `k ≥ 1`. -/
def StickyAt (W X d : Nat) : Prop :=
  ∀ k, 1 ≤ k → X / 10 ^ (k + d) = W / 10 ^ k ∧ W % 10 ^ k ≠ 0 ∧ X % 10 ^ (k + d) ≠ 0 ∧
    (2 * (W % 10 ^ k) ≥ 10 ^ k ↔ 2 * (X % 10 ^ (k + d)) ≥ 10 ^ (k + d)) ∧
    (2 * (W % 10 ^ k) > 10 ^ k ↔ 2 * (X % 10 ^ (k + d)) > 10 ^ (k + d)) ∧
    (2 * (W % 10 ^ k) = 10 ^ k ↔ 2 * (X % 10 ^ (k + d)) = 10 ^ (k + d))

/-- `_fix` of `X·10^(E-d)` is `_fix` of `W·10^E` when `W` has more than `prec` digits, `X` has `d`
more, and the digits `_fix` drops from them agree as `StickyAt` says. -/
theorem fixSpec_sticky (c : Ctx) (neg : Bool) (W X d : Nat) (E : Int) (fl : List Signal)
    (hW : c.prec < numDigits W) (hnd : numDigits X = numDigits W + d) (hs : StickyAt W X d) :
    fixSpec c neg X (E - d) fl = fixSpec c neg W E fl := by
  rw [fixSpec_round c neg X (E - d) fl (by omega), fixSpec_round c neg W E fl hW]
  have hae : ((numDigits X : Nat) : Int) + (E - d) = (numDigits W : Int) + E := by rw [hnd]; push_cast; omega
  have hm := Int.le_max_left ((numDigits W : Int) + E - c.prec) (c.emin - c.prec + 1)
  have hk1 : 1 ≤ fixK c W E := by unfold fixK; omega
  have hk : fixK c X (E - d) = fixK c W E + d := by
    unfold fixK; rw [hae]; omega
  rw [hae, hk]
  obtain ⟨hq, hr, hr', h1, h2, h3⟩ := hs (fixK c W E) hk1
  rw [hq, roundSpec_congr c.rounding neg (W / 10 ^ fixK c W E) _ _ _ _ hr' hr h1.symm h2.symm h3.symm]
  simp only [hr, hr', ne_eq, not_false_eq_true, decide_true]

/-! ## Signed coefficients -/

/-- `±n` as an int: `-n` when the sign bit is set. -/
def sgnI (s : Bool) (n : Nat) : Int := if s then -(n : Int) else n

theorem sgnI_natAbs (s : Bool) (n : Nat) : (sgnI s n).natAbs = n := by
  cases s <;> simp [sgnI]

theorem sgnI_lt (s : Bool) (n : Nat) (h : n ≠ 0) : decide (sgnI s n < 0) = s := by
  cases s <;> simp [sgnI] <;> omega

theorem sgnI_eq_zero (s : Bool) (n : Nat) : sgnI s n = 0 ↔ n = 0 := by
  cases s <;> simp [sgnI]

theorem sgnI_add_same (s : Bool) (a b : Nat) : sgnI s a + sgnI s b = sgnI s (a + b) := by
  cases s <;> simp [sgnI] <;> omega

theorem sgnI_add_opp (s : Bool) (a b : Nat) (h : b ≤ a) : sgnI s a + sgnI (!s) b = sgnI s (a - b) := by
  cases s <;> simp [sgnI] <;> omega

theorem exactSum_sgn (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int) :
    exactSum sa ca ea sb cb eb =
      sgnI sa (ca * 10 ^ (ea - min ea eb).toNat) + sgnI sb (cb * 10 ^ (eb - min ea eb).toNat) := by
  unfold exactSum; cases sa <;> cases sb <;> simp [sgnI] <;> omega

/-! ## `__add__` after `_normalize` -/

theorem strLimit_fix_run (c : Ctx) (rint : Nat) (s : Bool) (E : Int) (fl : List Signal) :
    (liftPy (strLimit rint) >>= fun _ => fix c (.fin s rint E)).run fl =
      if maxStrDigits < numDigits rint then .error (.valueError limitToStrMsg)
      else (fix c (.fin s rint E)).run fl := by
  rw [liftPy_run]
  by_cases h : numDigits rint > maxStrDigits
  · simp [strLimit, h]
  · simp [strLimit, h, show ¬ maxStrDigits < numDigits rint by omega]

/-- `__add__` of two non-zero finite operands once `_normalize` has brought them to one exponent `E`
(_pydecimal.py:1255-1286): opposite signs and equal coefficients give the zero of the
`negativezero` sign at `min(ea, eb)`; otherwise the signed sum of the working coefficients, whose
`str()` (:1285 for `result.int`) is subject to the int/str limit, goes through `_fix`. -/
theorem add_run_of_norm (c : Ctx) (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int)
    (fl : List Signal) (ha : ca ≠ 0) (hb : cb ≠ 0) (hl1 : numDigits ca ≤ maxStrDigits)
    (hl2 : numDigits cb ≤ maxStrDigits) (s1 s2 : Bool) (n1 n2 : Nat) (E : Int)
    (hw : workNormalize c.prec (sa, ca, ea) (sb, cb, eb) = .ok ((s1, n1, E), (s2, n2, E)))
    (h1 : n1 ≠ 0) (h2 : n2 ≠ 0) :
    (add c (.fin sa ca ea) (.fin sb cb eb)).run fl =
      if sgnI s1 n1 + sgnI s2 n2 = 0 then
        (fix c (.fin (decide (c.rounding = .floor ∧ sa ≠ sb)) 0 (min ea eb))).run fl
      else if maxStrDigits < numDigits (sgnI s1 n1 + sgnI s2 n2).natAbs then .error (.valueError limitToStrMsg)
      else (fix c (.fin (decide (sgnI s1 n1 + sgnI s2 n2 < 0)) (sgnI s1 n1 + sgnI s2 n2).natAbs E)).run fl := by
  have g1 : ¬ numDigits ca > maxStrDigits := by omega
  have g2 : ¬ numDigits cb > maxStrDigits := by omega
  simp only [add, ha, hb, and_self, ↓reduceIte, liftPy_run, intLimit, g1, g2, hw]
  -- the signed sum is `sgnI s n` with `n ≠ 0`, and the model reached `str(n)` then `_fix`
  have fin : ∀ (s : Bool) (n : Nat), n ≠ 0 → sgnI s1 n1 + sgnI s2 n2 = sgnI s n →
      StateT.run (do liftPy (strLimit n); fix c (Dec.fin s n E)) fl =
      if sgnI s1 n1 + sgnI s2 n2 = 0 then
        StateT.run (fix c (Dec.fin (decide (c.rounding = Rounding.floor ∧ sa ≠ sb)) 0 (min ea eb))) fl
      else if maxStrDigits < numDigits (sgnI s1 n1 + sgnI s2 n2).natAbs then
        Except.error (PyExc.valueError limitToStrMsg)
      else StateT.run (fix c (Dec.fin (decide (sgnI s1 n1 + sgnI s2 n2 < 0))
        (sgnI s1 n1 + sgnI s2 n2).natAbs E)) fl := by
    intro s n hn hs
    rw [hs, if_neg (by rw [sgnI_eq_zero]; exact hn), sgnI_natAbs, sgnI_lt s n hn]
    exact strLimit_fix_run c n s E fl
  cases s1 <;> cases s2
  · simp only [ne_eq, not_true_eq_false, ↓reduceIte]
    exact fin false (n1 + n2) (by omega) (sgnI_add_same _ _ _)
  · by_cases heq : n1 = n2
    · subst heq
      have h0 : sgnI false n1 + sgnI true n1 = 0 := by simp [sgnI]; omega
      simp only [ne_eq, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, h0]
    · by_cases hlt : n1 < n2
      · simp only [ne_eq, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, heq, hlt]
        refine fin true (n2 - n1) (by omega) ?_
        rw [Int.add_comm]; exact sgnI_add_opp true n2 n1 (by omega)
      · simp only [ne_eq, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, heq, hlt]
        exact fin false (n1 - n2) (by omega) (sgnI_add_opp false n1 n2 (by omega))
  · by_cases heq : n1 = n2
    · subst heq
      have h0 : sgnI true n1 + sgnI false n1 = 0 := by simp [sgnI]; omega
      simp only [ne_eq, Bool.true_eq_false, not_false_eq_true, ↓reduceIte, h0]
    · by_cases hlt : n1 < n2
      · simp only [ne_eq, Bool.true_eq_false, not_false_eq_true, ↓reduceIte, heq, hlt]
        refine fin false (n2 - n1) (by omega) ?_
        rw [Int.add_comm]; exact sgnI_add_opp false n2 n1 (by omega)
      · simp only [ne_eq, Bool.true_eq_false, not_false_eq_true, ↓reduceIte, heq, hlt]
        exact fin true (n1 - n2) (by omega) (sgnI_add_opp true n1 n2 (by omega))
  · simp only [ne_eq, not_true_eq_false, ↓reduceIte]
    exact fin true (n1 + n2) (by omega) (sgnI_add_same _ _ _)

end PyLean.Decimal
