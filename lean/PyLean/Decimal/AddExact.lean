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

/-! ## `_normalize` -/

/-- `exp = tmp.exp + min(-1, len(str(tmp.int)) - prec - 2)` (_pydecimal.py:5740). -/
def normX (p : Nat) (ct : Nat) (T : Int) : Int := T + min (-1) ((numDigits ct : Int) - p - 2)

/-- `other_len + other.exp - 1 < exp` (_pydecimal.py:5741): the other operand is below `10^exp`
and is replaced by `1·10^exp`. -/
def normSub (p : Nat) (ct : Nat) (T : Int) (co : Nat) (oe : Int) : Prop :=
  (numDigits co : Int) + oe - 1 < normX p ct T

instance (p ct T co oe) : Decidable (normSub p ct T co oe) := by unfold normSub; infer_instance

/-- The exponent both operands end at (_pydecimal.py:5741-5747): `exp` after the substitution,
else the other operand's own. -/
def normExp (p : Nat) (ct : Nat) (T : Int) (co : Nat) (oe : Int) : Int :=
  if normSub p ct T co oe then normX p ct T else oe

/-- The exponent `__add__` adds at: `_normalize` takes the operand with the larger exponent (the
first at equal exponents) as `tmp` (_pydecimal.py:5728-5733). -/
def addWorkExp (prec : Nat) (ca : Nat) (ea : Int) (cb : Nat) (eb : Int) : Int :=
  if ea < eb then normExp prec cb eb ca ea else normExp prec ca ea cb eb

/-- `_normalize(tmp, other, prec)` with `tmp` the operand of larger (or equal) exponent first. -/
theorem workNormalize_fst (p : Nat) (st so : Bool) (ct co : Nat) (T oe : Int)
    (h1 : numDigits ct ≤ maxStrDigits) (h2 : numDigits co ≤ maxStrDigits) (hT : oe ≤ T) :
    workNormalize p (st, ct, T) (so, co, oe) =
      .ok ((st, ct * 10 ^ (T - normExp p ct T co oe).toNat, normExp p ct T co oe),
        (so, if normSub p ct T co oe then 1 else co, normExp p ct T co oe)) := by
  have g1 : ¬ numDigits ct > maxStrDigits := by omega
  have g2 : ¬ numDigits co > maxStrDigits := by omega
  have hs : ¬ T < oe := by omega
  unfold normExp
  by_cases hsub : normSub p ct T co oe
  · have hsub' := hsub
    unfold normSub normX at hsub'
    simp [workNormalize, strLimit, g1, g2, hs, hsub, hsub', normX, bind, Except.bind, pure, Except.pure]
  · have hsub' := hsub
    unfold normSub normX at hsub'
    simp [workNormalize, strLimit, g1, g2, hs, hsub, hsub', bind, Except.bind, pure, Except.pure]

/-- `_normalize(other, tmp, prec)`: the operands swapped (`tmp` the second, of larger exponent). -/
theorem workNormalize_snd (p : Nat) (st so : Bool) (ct co : Nat) (T oe : Int)
    (h1 : numDigits ct ≤ maxStrDigits) (h2 : numDigits co ≤ maxStrDigits) (hT : oe < T) :
    workNormalize p (so, co, oe) (st, ct, T) =
      .ok ((so, if normSub p ct T co oe then 1 else co, normExp p ct T co oe),
        (st, ct * 10 ^ (T - normExp p ct T co oe).toNat, normExp p ct T co oe)) := by
  have g1 : ¬ numDigits ct > maxStrDigits := by omega
  have g2 : ¬ numDigits co > maxStrDigits := by omega
  unfold normExp
  by_cases hsub : normSub p ct T co oe
  · have hsub' := hsub
    unfold normSub normX at hsub'
    simp [workNormalize, strLimit, g1, g2, hT, hsub, hsub', normX, bind, Except.bind, pure, Except.pure]
  · have hsub' := hsub
    unfold normSub normX at hsub'
    simp [workNormalize, strLimit, g1, g2, hT, hsub, hsub', bind, Except.bind, pure, Except.pure]

theorem prec_lt_numDigits (p W : Nat) (hp : 1 ≤ p) (h : 10 ^ p ≤ W) : p < numDigits W := by
  by_cases h1 : numDigits W ≤ p
  · have := (numDigits_le_iff (by omega)).mp h1; omega
  · omega

/-- The sticky substitution, for one sign pattern: `±A` plus `±1` against `±A·10^d` plus `±o`,
with `A` a multiple of ten of more than `prec + 1` digits and `0 < o < 10^d`. -/
theorem sticky_pair (c : Ctx) (fl : List Signal) (hp : 1 ≤ c.prec) (st so : Bool) (A o d : Nat) (E : Int)
    (hA10 : A % 10 = 0) (hA : 10 ^ (c.prec + 1) ≤ A) (ho : o ≠ 0) (hod : o < 10 ^ d) :
    ∃ (s : Bool) (W X : Nat), sgnI st A + sgnI so 1 = sgnI s W ∧
      sgnI st (A * 10 ^ d) + sgnI so o = sgnI s X ∧ W ≠ 0 ∧ X ≠ 0 ∧
      numDigits X = numDigits W + d ∧ fixSpec c s X (E - d) fl = fixSpec c s W E fl := by
  have hp10 : 10 ^ c.prec * 10 = 10 ^ (c.prec + 1) := (Nat.pow_succ 10 c.prec).symm
  have hp1 : 10 ≤ 10 ^ c.prec := by
    have := Nat.pow_le_pow_right (show 0 < 10 by decide) hp; simpa using this
  have hm0 : 0 < 10 ^ d := Nat.pow_pos (by decide)
  have hAd : A ≤ A * 10 ^ d := Nat.le_mul_of_pos_right A hm0
  have hod' : o ≤ A * 10 ^ d := by
    have := Nat.mul_le_mul_right (10 ^ d) (show 1 ≤ A by omega); omega
  by_cases hs : st = so
  · subst hs
    refine ⟨st, A + 1, (A + 1 - 1) * 10 ^ d + o, sgnI_add_same _ _ _, ?_, by omega, by omega, ?_, ?_⟩
    · rw [Nat.add_sub_cancel]; exact sgnI_add_same _ _ _
    · exact numDigits_sticky_plus (A + 1) o d (by omega) (by omega) hod
    · exact fixSpec_sticky c st (A + 1) _ d E fl
        (prec_lt_numDigits _ _ hp (by omega))
        (numDigits_sticky_plus (A + 1) o d (by omega) (by omega) hod)
        (fun k hk => sticky_plus (A + 1) o d k (by omega) hk (by omega) hod)
  · have hso : so = !st := by cases st <;> cases so <;> simp_all
    subst hso
    refine ⟨st, A - 1, (A - 1 + 1) * 10 ^ d - o, sgnI_add_opp st A 1 (by omega), ?_, by omega, ?_, ?_, ?_⟩
    · rw [Nat.sub_add_cancel (show 1 ≤ A by omega)]; exact sgnI_add_opp st _ o hod'
    · rw [Nat.sub_add_cancel (show 1 ≤ A by omega)]
      have := Nat.mul_le_mul_right (10 ^ d) (show 1 ≤ A by omega)
      omega
    · exact numDigits_sticky_minus (A - 1) o d (by omega) (by omega) hod
    · exact fixSpec_sticky c st (A - 1) _ d E fl
        (prec_lt_numDigits _ _ hp (by omega))
        (numDigits_sticky_minus (A - 1) o d (by omega) (by omega) hod)
        (fun k hk => sticky_minus (A - 1) o d k (by omega) hk (by omega) hod)

/-- What `_normalize` leaves (`tmp` of exponent `T ≥ oe`): either the operands unchanged at the
other's exponent, or, after the substitution, a working sum that `_fix` rounds exactly as it
rounds the exact sum, with `E - oe` fewer digits. -/
theorem norm_core (c : Ctx) (fl : List Signal) (hp : 1 ≤ c.prec) (st so : Bool) (ct co : Nat)
    (T oe : Int) (hct : ct ≠ 0) (hco : co ≠ 0) (hT : oe ≤ T) :
    oe ≤ normExp c.prec ct T co oe ∧
    (¬ normSub c.prec ct T co oe →
      normExp c.prec ct T co oe = oe ∧
      sgnI st (ct * 10 ^ (T - normExp c.prec ct T co oe).toNat) + sgnI so co =
        sgnI st (ct * 10 ^ (T - oe).toNat) + sgnI so co) ∧
    (normSub c.prec ct T co oe →
      ∃ (s : Bool) (W X : Nat),
        sgnI st (ct * 10 ^ (T - normExp c.prec ct T co oe).toNat) + sgnI so 1 = sgnI s W ∧
        sgnI st (ct * 10 ^ (T - oe).toNat) + sgnI so co = sgnI s X ∧ W ≠ 0 ∧ X ≠ 0 ∧
        numDigits X = numDigits W + (normExp c.prec ct T co oe - oe).toNat ∧
        fixSpec c s X oe fl = fixSpec c s W (normExp c.prec ct T co oe) fl) := by
  have hmin := Int.min_le_left (-1 : Int) ((numDigits ct : Int) - c.prec - 2)
  have hmin2 := Int.min_le_right (-1 : Int) ((numDigits ct : Int) - c.prec - 2)
  have hmin3 : min (-1 : Int) ((numDigits ct : Int) - c.prec - 2) = -1 ∨
      min (-1 : Int) ((numDigits ct : Int) - c.prec - 2) = (numDigits ct : Int) - c.prec - 2 := by omega
  have hco1 := numDigits_pos co
  refine ⟨?_, fun hs => ?_, fun hs => ?_⟩
  · unfold normExp; split
    · rename_i h; unfold normSub at h; omega
    · omega
  · have hE : normExp c.prec ct T co oe = oe := by unfold normExp; simp [hs]
    exact ⟨hE, by rw [hE]⟩
  · have hE : normExp c.prec ct T co oe = normX c.prec ct T := by unfold normExp; simp [hs]
    have hs' := hs
    unfold normSub normX at hs'
    rw [hE]
    unfold normX
    generalize hX : T + min (-1 : Int) ((numDigits ct : Int) - c.prec - 2) = X at hs' ⊢
    -- d = X - oe ≥ len(co), t = T - X ≥ 1
    obtain ⟨d, hd⟩ : ∃ d : Nat, (X - oe).toNat = d := ⟨_, rfl⟩
    obtain ⟨t, ht⟩ : ∃ t : Nat, (T - X).toNat = t := ⟨_, rfl⟩
    have hdge : numDigits co ≤ d := by omega
    have ht1 : 1 ≤ t := by omega
    have htd : (T - oe).toNat = t + d := by omega
    have htp : c.prec + 2 ≤ numDigits ct + t := by omega
    rw [hd, ht, htd]
    have hcod : co < 10 ^ d :=
      Nat.lt_of_lt_of_le (lt_pow_numDigits co) (Nat.pow_le_pow_right (by decide) hdge)
    have hA10 : ct * 10 ^ t % 10 = 0 := by
      rw [Nat.mul_mod, pow_mod_ten ht1]; simp
    have hA : 10 ^ (c.prec + 1) ≤ ct * 10 ^ t := by
      have h1 := pow_numDigits_le hct
      have h2 : 10 ^ (c.prec + 1) ≤ 10 ^ (numDigits ct - 1) * 10 ^ t := by
        rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
      exact Nat.le_trans h2 (Nat.mul_le_mul_right _ h1)
    obtain ⟨s, W, X', h1, h2, h3, h4, h5, h6⟩ :=
      sticky_pair c fl hp st so (ct * 10 ^ t) co d X hA10 hA hco hcod
    refine ⟨s, W, X', h1, ?_, h3, h4, h5, ?_⟩
    · rw [Nat.pow_add, ← Nat.mul_assoc]; exact h2
    · rw [show oe = X - (d : Int) by omega]; exact h6

end PyLean.Decimal
