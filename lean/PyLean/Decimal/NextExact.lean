import PyLean.Decimal.AddExact
import PyLean.Decimal.DelegateExact

/-!
`next_plus`, `next_minus` and `next_toward`: the smallest representable number above (largest
below) a finite operand, and the twin relation between them.

A value is *representable* in a context when it is `±cz·10^ez` with `cz < 10^prec` and
`Etiny ≤ ez ≤ Etop` (`RepAt`): every value `_fix` returns has that form (a finite value of
exponent above `Etop`, which `clamp=0` allows, is the same number as one at `Etop` with trailing
zeros). Values are compared as integers after scaling to a common exponent `L` (`scl`).
-/

namespace PyLean.Decimal

open PyLean

/-- `±c·10^(e-L)` as an integer, for `L ≤ e`. -/
def scl (neg : Bool) (c : Nat) (e L : Int) : Int :=
  if neg then -((c * 10 ^ (e - L).toNat : Nat) : Int) else ((c * 10 ^ (e - L).toNat : Nat) : Int)

/-- `Z` is, scaled to the exponent `L`, a value representable in `c`: `±cz·10^ez` with
`cz < 10^prec` and `Etiny ≤ ez ≤ Etop`. -/
def RepAt (c : Ctx) (L : Int) (Z : Int) : Prop :=
  ∃ (b : Bool) (cz : Nat) (ez : Int), cz < 10 ^ c.prec ∧ c.etiny ≤ ez ∧ ez ≤ c.etop ∧ Z = scl b cz ez L

/-! ## Arithmetic on powers of ten -/

theorem pow10_le {a b : Nat} (h : a ≤ b) : 10 ^ a ≤ 10 ^ b := Nat.pow_le_pow_right (by decide) h

theorem pow10_pos (a : Nat) : 0 < 10 ^ a := Nat.pow_pos (by decide)

/-- A representable magnitude is at most the largest finite value. -/
theorem rep_le_max {p : Nat} {cz a aU : Nat} (hc : cz < 10 ^ p) (ha : a ≤ aU) :
    cz * 10 ^ a ≤ (10 ^ p - 1) * 10 ^ aU :=
  Nat.mul_le_mul (by omega) (pow10_le ha)

/-- A magnitude below `10^p` at an exponent below `m` is below `10^(p-1)·10^m`. -/
theorem small_lt {p : Nat} (hp : 1 ≤ p) {cz a m : Nat} (hc : cz < 10 ^ p) (ha : a + 1 ≤ m) :
    cz * 10 ^ a < 10 ^ (p - 1) * 10 ^ m := by
  have h1 : cz * 10 ^ a < 10 ^ p * 10 ^ a := Nat.mul_lt_mul_of_pos_right hc (pow10_pos a)
  have h2 : 10 ^ p * 10 ^ a ≤ 10 ^ (p - 1) * 10 ^ m := by
    rw [← Nat.pow_add, ← Nat.pow_add]; exact pow10_le (by omega)
  omega

/-- A magnitude at an exponent of at least `m` is a multiple of `10^m`. -/
theorem mult_of_ge {cz a m : Nat} (ha : m ≤ a) : cz * 10 ^ a = (cz * 10 ^ (a - m)) * 10 ^ m := by
  rw [Nat.mul_assoc, ← Nat.pow_add, Nat.sub_add_cancel ha]

/-- `(q0 + 1)·M` is the least multiple of `M` above `q0·M`. -/
theorem mult_succ_le {w q M : Nat} (h : q * M < w * M) : (q + 1) * M ≤ w * M :=
  Nat.mul_le_mul_right M (Nat.lt_of_mul_lt_mul_right h)

theorem mult_le_of_lt_succ {w q M : Nat} (h : w * M < (q + 1) * M) : w * M ≤ q * M :=
  Nat.mul_le_mul_right M (Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_right h))

/-- A coefficient of `nd` digits at exponent `b` is at least `10^(nd-1+b)`. -/
theorem co_ge {co : Nat} (hc : co ≠ 0) (b : Nat) : 10 ^ (numDigits co - 1 + b) ≤ co * 10 ^ b := by
  rw [Nat.pow_add]
  exact Nat.mul_le_mul_right _ (numDigits_bounds hc).1

/-! ## Rounding toward +∞ is the least representable value at or above -/

/-- `sigRun` in a context that traps nothing returns its value. -/
theorem sigRun_noTraps (c : Ctx) (h : c.traps = []) : ∀ (ss fl : List Signal) (v : Dec),
    ∃ fl', sigRun c ss fl v = .ok (v, fl')
  | [], fl, v => ⟨fl, rfl⟩
  | s :: ss, fl, v => by
    have : s ∉ c.traps := by rw [h]; simp
    simp only [sigRun, this, ↓reduceIte]
    exact sigRun_noTraps c h ss _ v

theorem sigRun_val {c : Ctx} (h : c.traps = []) {ss fl fl1 : List Signal} {v w : Dec}
    (hr : sigRun c ss fl v = .ok (w, fl1)) : w = v := by
  obtain ⟨fl', h'⟩ := sigRun_noTraps c h ss fl v
  rw [h'] at hr
  cases hr
  rfl

/-- What rounding toward `+∞` into `c` gives for the value `X` (scaled to `L`): `+Infinity` when
every representable value is below `X`; otherwise a finite `±cv·10^ev` with `ev ≥ Etiny`, at least
`X`, at most every representable value at least `X`, and either `X` itself or representable. -/
def CeilGoal (c : Ctx) (L X : Int) (v : Dec) : Prop :=
  (v = .inf false ∧ ∀ Z, RepAt c L Z → Z < X) ∨
  (∃ sv cv ev, v = .fin sv cv ev ∧ c.etiny ≤ ev ∧ X ≤ scl sv cv ev L ∧
     (scl sv cv ev L = X ∨ (cv < 10 ^ c.prec ∧ ev ≤ c.etop)) ∧
     ∀ Z, RepAt c L Z → X ≤ Z → scl sv cv ev L ≤ Z)

/-- A representable value, unpacked at `L ≤ Etiny`. -/
theorem repAt_cases {c : Ctx} {L Z : Int} (hL : L ≤ c.etiny) (h : RepAt c L Z) :
    ∃ (bz : Bool) (cz az : Nat), cz < 10 ^ c.prec ∧ (c.etiny - L).toNat ≤ az ∧ az ≤ (c.etop - L).toNat ∧
      Z = (if bz then -((cz * 10 ^ az : Nat) : Int) else ((cz * 10 ^ az : Nat) : Int)) := by
  obtain ⟨bz, cz, ez, hc, h1, h2, rfl⟩ := h
  exact ⟨bz, cz, (ez - L).toNat, hc, by omega, by omega, rfl⟩

/-- Every representable value lies within the largest finite magnitude. -/
theorem repAt_bound {c : Ctx} {L Z : Int} (hL : L ≤ c.etiny) (h : RepAt c L Z) :
    Z ≤ (((10 ^ c.prec - 1) * 10 ^ (c.etop - L).toNat : Nat) : Int) ∧
    -(((10 ^ c.prec - 1) * 10 ^ (c.etop - L).toNat : Nat) : Int) ≤ Z := by
  obtain ⟨bz, cz, az, hc, _, h2, rfl⟩ := repAt_cases hL h
  have := rep_le_max hc h2
  cases bz <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem overflowResult_ceiling (q : Ctx) (h : q.rounding = .ceiling) (neg : Bool) :
    overflowResult q neg = if neg then .fin true (10 ^ q.prec - 1) (q.emax - q.prec + 1) else .inf false := by
  cases neg <;> simp [overflowResult, h]

/-- The overflow branch: a value above every finite one. -/
theorem ceil_over (q : Ctx) (hp : 1 ≤ q.prec) (hE : q.emin ≤ q.emax) (hr : q.rounding = .ceiling)
    (neg : Bool) (co : Nat) (e L : Int) (hc : co ≠ 0) (hL1 : L ≤ e) (hL2 : L ≤ q.etiny)
    (ho : e + (numDigits co : Int) - 1 > q.emax) :
    CeilGoal q L (scl neg co e L) (overflowResult q neg) := by
  have hT : q.etiny = q.emin - q.prec + 1 := rfl
  have hU : q.etop = q.emax - q.prec + 1 := rfl
  have hbig : (10 ^ q.prec - 1) * 10 ^ (q.etop - L).toNat < co * 10 ^ (e - L).toNat := by
    have h1 := co_ge hc (e - L).toNat
    have h2 : 10 ^ (q.prec + (q.etop - L).toNat) ≤ 10 ^ (numDigits co - 1 + (e - L).toNat) :=
      pow10_le (by omega)
    have h3 : (10 ^ q.prec - 1) * 10 ^ (q.etop - L).toNat < 10 ^ q.prec * 10 ^ (q.etop - L).toNat :=
      Nat.mul_lt_mul_of_pos_right (by have := pow10_pos q.prec; omega) (pow10_pos _)
    rw [← Nat.pow_add] at h3
    omega
  rw [overflowResult_ceiling q hr]
  cases neg with
  | false =>
    left
    refine ⟨rfl, fun Z hZ => ?_⟩
    have := (repAt_bound hL2 hZ).1
    simp only [scl, Bool.false_eq_true, ↓reduceIte]
    omega
  | true =>
    right
    refine ⟨true, 10 ^ q.prec - 1, q.emax - q.prec + 1, rfl, by omega, ?_, Or.inr ⟨by have := pow10_pos q.prec; omega, by omega⟩, ?_⟩
    · have e1 : (q.emax - q.prec + 1 - L).toNat = (q.etop - L).toNat := by rw [hU]
      simp only [scl, ↓reduceIte, e1]
      omega
    · intro Z hZ _
      have := (repAt_bound hL2 hZ).2
      have e1 : (q.emax - q.prec + 1 - L).toNat = (q.etop - L).toNat := by rw [hU]
      simp only [scl, ↓reduceIte, e1]
      omega

/-- The branch that keeps the value: it is the operand itself. -/
theorem ceil_keep (q : Ctx) (neg : Bool) (cv : Nat) (ev : Int) (co : Nat) (e L : Int)
    (hT : q.etiny ≤ ev) (hv : scl neg cv ev L = scl neg co e L) :
    CeilGoal q L (scl neg co e L) (.fin neg cv ev) := by
  right
  exact ⟨neg, cv, ev, rfl, hT, Int.le_of_eq hv.symm, Or.inl hv, fun Z _ hZ => by rw [hv]; exact hZ⟩

theorem scl_fold (neg : Bool) (co : Nat) (e U L : Int) (hU : U < e) (hL : L ≤ U) :
    scl neg (co * 10 ^ (e - U).toNat) U L = scl neg co e L := by
  have : co * 10 ^ (e - U).toNat * 10 ^ (U - L).toNat = co * 10 ^ (e - L).toNat := by
    rw [Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    omega
  simp only [scl, this]

/-- Leastness above: a representable value at least `q0·M + rb` (with `0 < rb`) is at least
`(q0+1)·M`, when every representable value at an exponent below `M`'s has a magnitude below
`q0·M`. -/
theorem least_pos {c : Ctx} {L Z : Int} (hL : L ≤ c.etiny) (hZ : RepAt c L Z) (q0 rb m : Nat)
    (hrb : 0 < rb) (hX : (((q0 * 10 ^ m + rb : Nat)) : Int) ≤ Z)
    (hsm : ∀ cz az, cz < 10 ^ c.prec → (c.etiny - L).toNat ≤ az → az < m → cz * 10 ^ az < q0 * 10 ^ m) :
    (((q0 + 1) * 10 ^ m : Nat) : Int) ≤ Z := by
  obtain ⟨bz, cz, az, hc, h1, _, rfl⟩ := repAt_cases hL hZ
  cases bz with
  | true => simp only [↓reduceIte] at hX; omega
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hX ⊢
    by_cases ha : m ≤ az
    · rw [mult_of_ge ha] at hX ⊢
      have : q0 * 10 ^ m < cz * 10 ^ (az - m) * 10 ^ m := by omega
      have := mult_succ_le this
      omega
    · have := hsm cz az hc h1 (by omega)
      omega

/-- Leastness below zero: a representable value at least `-(q0·M + rb)` (with `rb < M`) is at
least `-(q0·M)`. -/
theorem least_neg {c : Ctx} {L Z : Int} (hL : L ≤ c.etiny) (hZ : RepAt c L Z) (q0 rb m : Nat)
    (hrb : rb < 10 ^ m) (hX : -(((q0 * 10 ^ m + rb : Nat)) : Int) ≤ Z)
    (hsm : ∀ cz az, cz < 10 ^ c.prec → (c.etiny - L).toNat ≤ az → az < m → cz * 10 ^ az < q0 * 10 ^ m) :
    -((q0 * 10 ^ m : Nat) : Int) ≤ Z := by
  obtain ⟨bz, cz, az, hc, h1, _, rfl⟩ := repAt_cases hL hZ
  cases bz with
  | false => simp only [Bool.false_eq_true, ↓reduceIte]; omega
  | true =>
    simp only [↓reduceIte] at hX ⊢
    by_cases ha : m ≤ az
    · rw [mult_of_ge ha] at hX ⊢
      have h2 : cz * 10 ^ (az - m) * 10 ^ m < (q0 + 1) * 10 ^ m := by rw [Nat.succ_mul]; omega
      have := mult_le_of_lt_succ h2
      omega
    · have := hsm cz az hc h1 (by omega)
      omega

/-- The rounding branch of `_fix` under `ROUND_CEILING`: the kept prefix `q0` of `co`, plus one
when digits that are not all zero are dropped from a positive value, at the exponent `emn`. -/
theorem ceil_round (q : Ctx) (hp : 1 ≤ q.prec) (hE : q.emin ≤ q.emax) (hr : q.rounding = .ceiling)
    (neg : Bool) (co : Nat) (e L emn : Int) (k : Nat) (hc : co ≠ 0) (hL1 : L ≤ e) (hL2 : L ≤ q.etiny)
    (hemn1 : (numDigits co : Int) + e - q.prec ≤ emn) (hemn2 : q.emin - q.prec + 1 ≤ emn)
    (hemn3 : emn = (numDigits co : Int) + e - q.prec ∨ emn = q.emin - q.prec + 1)
    (hno : ¬ e + (numDigits co : Int) - 1 > q.emax) (hlt : e < emn) (hk : (k : Int) = emn - e) :
    CeilGoal q L (scl neg co e L)
      (if decide ((if numDigits (roundSpec .ceiling neg (co / 10 ^ k) (co % 10 ^ k) (10 ^ k)) > q.prec
            then emn + 1 else emn) > q.emax - q.prec + 1) = true
        then overflowResult q neg
        else .fin neg (if numDigits (roundSpec .ceiling neg (co / 10 ^ k) (co % 10 ^ k) (10 ^ k)) > q.prec
            then roundSpec .ceiling neg (co / 10 ^ k) (co % 10 ^ k) (10 ^ k) / 10
            else roundSpec .ceiling neg (co / 10 ^ k) (co % 10 ^ k) (10 ^ k))
          (if numDigits (roundSpec .ceiling neg (co / 10 ^ k) (co % 10 ^ k) (10 ^ k)) > q.prec
            then emn + 1 else emn)) := by
  have hT : q.etiny = q.emin - q.prec + 1 := rfl
  have hU : q.etop = q.emax - q.prec + 1 := rfl
  obtain ⟨b, hb⟩ : ∃ b : Nat, (b : Int) = e - L := ⟨(e - L).toNat, by omega⟩
  have heb : (e - L).toNat = b := by omega
  have hemb : (emn - L).toNat = b + k := by omega
  have hemb1 : (emn + 1 - L).toNat = b + k + 1 := by omega
  have hrk : co % 10 ^ k < 10 ^ k := Nat.mod_lt _ (pow10_pos k)
  have hco := Nat.div_add_mod co (10 ^ k)
  have hnd := (numDigits_bounds hc)
  have hq0lt : co / 10 ^ k < 10 ^ q.prec := by
    rw [Nat.div_lt_iff_lt_mul (pow10_pos k), ← Nat.pow_add]
    exact Nat.lt_of_lt_of_le hnd.2 (pow10_le (by omega))
  have hq0big : emn ≠ q.emin - q.prec + 1 → 10 ^ (q.prec - 1) ≤ co / 10 ^ k := by
    intro hne
    rw [Nat.le_div_iff_mul_le (pow10_pos k), ← Nat.pow_add]
    exact Nat.le_trans (pow10_le (by omega)) hnd.1
  have hemnU : emn ≤ q.emax - q.prec + 1 := by omega
  generalize co / 10 ^ k = q0 at *
  generalize co % 10 ^ k = r at *
  have hM : 10 ^ (b + k) = 10 ^ k * 10 ^ b := by rw [Nat.pow_add, Nat.mul_comm]
  have hX : co * 10 ^ b = q0 * 10 ^ (b + k) + r * 10 ^ b := by
    rw [← hco, hM, Nat.add_mul]
    congr 1
    rw [Nat.mul_comm (10 ^ k) q0, Nat.mul_assoc]
  have hrb : r * 10 ^ b < 10 ^ (b + k) := by
    rw [hM]; exact Nat.mul_lt_mul_of_pos_right hrk (pow10_pos b)
  have hsm : ∀ cz az, cz < 10 ^ q.prec → (q.etiny - L).toNat ≤ az → az < b + k →
      cz * 10 ^ az < q0 * 10 ^ (b + k) := by
    intro cz az hcz h1 h2
    have := hq0big (by omega)
    exact Nat.lt_of_lt_of_le (small_lt hp hcz (by omega)) (Nat.mul_le_mul_right _ this)
  have hq0d : ¬ numDigits q0 > q.prec := by
    have := (numDigits_le_iff (by omega : 0 < q.prec)).mpr hq0lt; omega
  cases neg with
  | true =>
    have hq : roundSpec .ceiling true q0 r (10 ^ k) = q0 := by simp [roundSpec]
    have hov : ¬ (emn > q.emax - q.prec + 1) := by omega
    simp only [hq, hq0d, ↓reduceIte, hov, decide_false, Bool.false_eq_true]
    right
    refine ⟨true, q0, emn, rfl, by omega, ?_, Or.inr ⟨hq0lt, by omega⟩, ?_⟩
    · simp only [scl, ↓reduceIte, heb, hemb, hX]; omega
    · intro Z hZ hXZ
      simp only [scl, ↓reduceIte, heb, hX] at hXZ
      simp only [scl, ↓reduceIte, hemb]
      exact least_neg hL2 hZ q0 (r * 10 ^ b) (b + k) hrb hXZ hsm
  | false =>
    by_cases hr0 : r = 0
    · subst hr0
      have hq : roundSpec .ceiling false q0 0 (10 ^ k) = q0 := by simp [roundSpec]
      have hov : ¬ (emn > q.emax - q.prec + 1) := by omega
      simp only [hq, hq0d, ↓reduceIte, hov, decide_false, Bool.false_eq_true]
      apply ceil_keep q false q0 emn co e L (by omega)
      simp only [scl, Bool.false_eq_true, ↓reduceIte, heb, hemb, hX, Nat.zero_mul, Nat.add_zero]
    · have hq : roundSpec .ceiling false q0 r (10 ^ k) = q0 + 1 := by simp [roundSpec, hr0]
      have hrb0 : 0 < r * 10 ^ b := Nat.mul_pos (by omega) (pow10_pos b)
      have hXv : scl false co e L = ((q0 * 10 ^ (b + k) + r * 10 ^ b : Nat) : Int) := by
        simp only [scl, Bool.false_eq_true, ↓reduceIte, heb, hX]
      simp only [hq]
      by_cases hd : numDigits (q0 + 1) > q.prec
      · have h10 : q0 + 1 = 10 ^ q.prec := by
          have : ¬ (q0 + 1 < 10 ^ q.prec) := fun h =>
            absurd ((numDigits_le_iff (by omega : 0 < q.prec)).mpr h) (by omega)
          omega
        simp only [hd, ↓reduceIte]
        by_cases hov : emn + 1 > q.emax - q.prec + 1
        · simp only [hov, decide_true, ↓reduceIte, overflowResult_ceiling q hr, Bool.false_eq_true]
          left
          refine ⟨rfl, fun Z hZ => ?_⟩
          have hb' := (repAt_bound hL2 hZ).1
          have e1 : (q.etop - L).toNat = b + k := by rw [hU]; omega
          rw [e1] at hb'
          have : 10 ^ q.prec - 1 = q0 := by omega
          rw [this] at hb'
          rw [hXv]; omega
        · simp only [hov, decide_false, ↓reduceIte, Bool.false_eq_true]
          have hV : (q0 + 1) / 10 * 10 ^ (b + k + 1) = (q0 + 1) * 10 ^ (b + k) := by
            rw [h10]
            obtain ⟨j, hj⟩ : ∃ j, q.prec = j + 1 := ⟨q.prec - 1, by omega⟩
            have h1 : 10 ^ (j + 1) / 10 = 10 ^ j := by
              rw [Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]
            rw [hj, h1, ← Nat.pow_add, ← Nat.pow_add]
            congr 1
            omega
          have hS : (q0 + 1) * 10 ^ (b + k) = q0 * 10 ^ (b + k) + 10 ^ (b + k) := by
            rw [Nat.add_mul, Nat.one_mul]
          right
          refine ⟨false, (q0 + 1) / 10, emn + 1, rfl, by omega, ?_, Or.inr ⟨?_, by omega⟩, ?_⟩
          · rw [hXv]; simp only [scl, Bool.false_eq_true, ↓reduceIte, hemb1, hV, hS]
            omega
          · exact Nat.lt_of_lt_of_le (Nat.div_lt_self (by omega) (by decide)) (by omega)
          · intro Z hZ hXZ
            simp only [scl, Bool.false_eq_true, ↓reduceIte, hemb1, hV]
            rw [hXv] at hXZ
            exact least_pos hL2 hZ q0 (r * 10 ^ b) (b + k) hrb0 hXZ hsm
      · have hov : ¬ (emn > q.emax - q.prec + 1) := by omega
        simp only [hd, ↓reduceIte, hov, decide_false, Bool.false_eq_true]
        right
        refine ⟨false, q0 + 1, emn, rfl, by omega, ?_, Or.inr ⟨?_, by omega⟩, ?_⟩
        · have hS : (q0 + 1) * 10 ^ (b + k) = q0 * 10 ^ (b + k) + 10 ^ (b + k) := by
            rw [Nat.add_mul, Nat.one_mul]
          rw [hXv]; simp only [scl, Bool.false_eq_true, ↓reduceIte, hemb, hS]
          omega
        · exact (numDigits_le_iff (by omega : 0 < q.prec)).mp (by omega)
        · intro Z hZ hXZ
          simp only [scl, Bool.false_eq_true, ↓reduceIte, hemb]
          rw [hXv] at hXZ
          exact least_pos hL2 hZ q0 (r * 10 ^ b) (b + k) hrb0 hXZ hsm

/-- `_fix` under `ROUND_CEILING`, in a context that traps nothing, of every finite non-zero value:
the least representable value at or above it (`CeilGoal`). -/
theorem ceil_fixSpec (q : Ctx) (hp : 1 ≤ q.prec) (hE : q.emin ≤ q.emax) (hr : q.rounding = .ceiling)
    (htr : q.traps = []) (neg : Bool) (co : Nat) (e L : Int) (hc : co ≠ 0) (hL1 : L ≤ e)
    (hL2 : L ≤ q.etiny) (fl0 fl1 : List Signal) (v : Dec) (h : fixSpec q neg co e fl0 = .ok (v, fl1)) :
    CeilGoal q L (scl neg co e L) v := by
  have hT : q.etiny = q.emin - q.prec + 1 := rfl
  have hU : q.etop = q.emax - q.prec + 1 := rfl
  unfold fixSpec at h
  simp only at h
  split at h
  · rename_i ho
    rw [sigRun_val htr h]
    exact ceil_over q hp hE hr neg co e L hc hL1 hL2 ho
  · rename_i ho
    split at h
    · rename_i hk
      split at h
      · rename_i hcl
        rw [sigRun_val htr h]
        exact ceil_keep q neg _ _ co e L (by omega) (scl_fold neg co e _ L hcl.2 (by omega))
      · rw [sigRun_val htr h]
        exact ceil_keep q neg co e co e L (by omega) rfl
    · rename_i hk
      split at h
      · exact absurd h (by simp)
      · rw [sigRun_val htr h]
        simp only [hr]
        exact ceil_round q hp hE hr neg co e L _ _ hc hL1 hL2 (Int.le_max_left _ _) (Int.le_max_right _ _)
          (by omega) ho (by omega) (by omega)

/-- What `next_plus` gives for the value `X` (scaled to `L`): `+Infinity` when no representable
value is above `X`, otherwise the least representable value above it. -/
def NextGoal (c : Ctx) (L X : Int) (y : Dec) : Prop :=
  (y = .inf false ∧ ∀ Z, RepAt c L Z → Z ≤ X) ∨
  (∃ sy cy ey, y = .fin sy cy ey ∧ cy < 10 ^ c.prec ∧ c.etiny ≤ ey ∧ ey ≤ c.etop ∧
     X < scl sy cy ey L ∧ ∀ Z, RepAt c L Z → X < Z → scl sy cy ey L ≤ Z)

/-- A rounded value that differs from the operand is the least representable value above it. -/
theorem next_of_ceil_ne {c : Ctx} {L X : Int} {v : Dec} (h : CeilGoal c L X v)
    (hne : ∀ sv cv ev, v = .fin sv cv ev → c.etiny ≤ ev → scl sv cv ev L ≠ X) : NextGoal c L X v := by
  rcases h with ⟨rfl, h2⟩ | ⟨sv, cv, ev, rfl, h1, h2, h3, h4⟩
  · exact Or.inl ⟨rfl, fun Z hZ => Int.le_of_lt (h2 Z hZ)⟩
  · have hn := hne sv cv ev rfl h1
    rcases h3 with h3 | ⟨h3, h3'⟩
    · exact absurd h3 hn
    · exact Or.inr ⟨sv, cv, ev, rfl, h3, h1, h3', by omega, fun Z hZ hXZ => h4 Z hZ (by omega)⟩

/-- `10^(Etiny - L)` as an integer, for `L < Etiny`. -/
def gapD (c : Ctx) (L : Int) : Int := ((10 ^ (c.etiny - L).toNat : Nat) : Int)
def gapd (c : Ctx) (L : Int) : Int := ((10 ^ (c.etiny - 1 - L).toNat : Nat) : Int)

theorem gapD_eq {c : Ctx} {L : Int} (hL : L < c.etiny) : gapD c L = 10 * gapd c L := by
  have : (c.etiny - L).toNat = (c.etiny - 1 - L).toNat + 1 := by omega
  simp only [gapD, gapd, this, Nat.pow_succ]
  omega

theorem gapd_pos (c : Ctx) (L : Int) : 0 < gapd c L := by
  have := pow10_pos (c.etiny - 1 - L).toNat
  simp only [gapd]; omega

/-- Values on the grid of `10^Etiny`: from `u·D < w·D`, `w·D ≥ u·D + D`. -/
theorem grid_step {u w D : Int} (hD : 0 < D) (h : u * D < w * D) : u * D + D ≤ w * D := by
  have h1 : u < w := Int.lt_of_mul_lt_mul_right h (by omega)
  have h2 : 1 * D ≤ (w - u) * D := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
  rw [Int.sub_mul, Int.one_mul] at h2
  omega

/-- A finite value at an exponent of at least `Etiny` is on the grid of `10^Etiny`. -/
theorem fin_grid (c : Ctx) (L : Int) (sv : Bool) (cv : Nat) (ev : Int) (hT : c.etiny ≤ ev) (hL : L ≤ c.etiny) :
    ∃ w : Int, scl sv cv ev L = w * gapD c L := by
  have h := mult_of_ge (cz := cv) (show (c.etiny - L).toNat ≤ (ev - L).toNat by omega)
  refine ⟨sgnVal sv (cv * 10 ^ ((ev - L).toNat - (c.etiny - L).toNat)), ?_⟩
  simp only [scl, gapD, sgnVal, h]
  cases sv <;> simp [Int.natCast_mul, Int.neg_mul]

theorem repAt_grid {c : Ctx} {L Z : Int} (hL : L ≤ c.etiny) (hZ : RepAt c L Z) :
    ∃ w : Int, Z = w * gapD c L := by
  obtain ⟨b, cz, ez, _, h1, _, rfl⟩ := hZ
  exact fin_grid c L b cz ez h1 hL

/-- `next_plus` after the rounding returned the operand itself: the value one tenth of a unit
of `Etiny` above it, rounded up, is the least representable value above the operand. -/
theorem next_of_ceil_add {c : Ctx} {L X : Int} {y : Dec} (hL : L < c.etiny) (hX : ∃ u, X = u * gapD c L)
    (h : CeilGoal c L (X + gapd c L) y) : NextGoal c L X y := by
  obtain ⟨u, rfl⟩ := hX
  have hD := gapD_eq hL
  have hd := gapd_pos c L
  have hDp : 0 < gapD c L := by omega
  rcases h with ⟨rfl, h2⟩ | ⟨sy, cy, ey, rfl, h1, h2, h3, h4⟩
  · refine Or.inl ⟨rfl, fun Z hZ => ?_⟩
    have := h2 Z hZ
    obtain ⟨w, rfl⟩ := repAt_grid (by omega) hZ
    by_cases hc : u * gapD c L < w * gapD c L
    · have := grid_step hDp hc; omega
    · omega
  · obtain ⟨w, hw⟩ := fin_grid c L sy cy ey h1 (by omega)
    have hne : scl sy cy ey L ≠ u * gapD c L + gapd c L := by
      rw [hw]; intro heq
      by_cases hc : u * gapD c L < w * gapD c L
      · have := grid_step hDp hc; omega
      · omega
    rcases h3 with h3 | ⟨h3, h3'⟩
    · exact absurd h3 hne
    · refine Or.inr ⟨sy, cy, ey, rfl, h3, h1, h3', by omega, fun Z hZ hXZ => h4 Z hZ ?_⟩
      obtain ⟨w', rfl⟩ := repAt_grid (by omega) hZ
      have := grid_step hDp hXZ; omega

/-! ## `next_plus` on a finite operand -/

/-- The body of `next_plus` on a finite operand (_pydecimal.py:3612-3619): `_fix` under
`ROUND_CEILING` in a copy that ignores every flag, then the sum with `1E(Etiny-1)` when that left
the value unchanged; the caller's flags are untouched. -/
theorem nextPlus_fin_run (c : Ctx) (s : Bool) (co : Nat) (e : Int) (fl : List Signal) :
    (nextPlus c (.fin s co e)).run fl =
      match (fix (quietCtx c .ceiling) (.fin s co e)).run fl with
      | .error x => .error x
      | .ok (v, fl2) =>
        if cmpVal v (.fin s co e) ≠ .eq then .ok (v, fl)
        else match (add (quietCtx c .ceiling) (.fin s co e)
            (.fin false 1 ((quietCtx c .ceiling).etiny - 1))).run fl2 with
          | .error x => .error x
          | .ok (y, _) => .ok (y, fl) := by
  simp only [nextPlus, checkNans, isinfinity, StateT.run, bind, StateT.bind, pure, StateT.pure,
    Except.bind, Except.pure]
  simp only [show ¬ ((0 : Int) = 1) by decide, show ¬ ((0 : Int) = -1) by decide, ↓reduceIte]
  unfold quietly
  simp only [StateT.bind, bind, Except.bind, pure, Except.pure]
  cases fix (quietCtx c .ceiling) (.fin s co e) fl with
  | error x => rfl
  | ok p =>
    obtain ⟨v, fl2⟩ := p
    simp only
    by_cases hc : cmpVal v (.fin s co e) ≠ .eq
    · simp only [hc, ↓reduceIte, ne_eq, not_false_eq_true]; rfl
    · simp only [hc, ↓reduceIte]
      cases add (quietCtx c .ceiling) (.fin s co e) (.fin false 1 ((quietCtx c .ceiling).etiny - 1)) fl2 with
      | error x => rfl
      | ok p => rfl

theorem ordOf_eq_iff (x y : Int) : ordOf x y = .eq ↔ x = y := by
  unfold ordOf
  by_cases h1 : x < y
  · simp only [h1, ↓reduceIte, reduceCtorEq, false_iff]; omega
  · by_cases h2 : x = y <;> simp [h1, h2]

theorem scl_split (n : Bool) (c : Nat) (e m L : Int) (h1 : m ≤ e) (h2 : L ≤ m) :
    scl n c e L = sgnVal n (c * 10 ^ (e - m).toNat) * ((10 ^ (m - L).toNat : Nat) : Int) := by
  have : (e - L).toNat = (e - m).toNat + (m - L).toNat := by omega
  simp only [scl, sgnVal, this, Nat.pow_add, ← Nat.mul_assoc]
  cases n <;> simp [Int.natCast_mul, Int.neg_mul]

/-- `_cmp` finds two finite values equal exactly when they agree scaled to any lower exponent. -/
theorem finOrder_eq_iff (n1 : Bool) (c1 : Nat) (e1 : Int) (n2 : Bool) (c2 : Nat) (e2 L : Int)
    (h1 : L ≤ e1) (h2 : L ≤ e2) :
    finOrder n1 c1 e1 n2 c2 e2 = .eq ↔ scl n1 c1 e1 L = scl n2 c2 e2 L := by
  unfold finOrder
  rw [ordOf_eq_iff, scl_split n1 c1 e1 (min e1 e2) L (by omega) (by omega),
    scl_split n2 c2 e2 (min e1 e2) L (by omega) (by omega)]
  have hD : ((10 ^ (min e1 e2 - L).toNat : Nat) : Int) ≠ 0 := by
    have := pow10_pos (min e1 e2 - L).toNat; omega
  constructor
  · intro h; rw [h]
  · intro h; exact Int.eq_of_mul_eq_mul_right hD h

theorem scl_natAbs (x L : Int) : scl (decide (x < 0)) x.natAbs L L = x := by
  by_cases hx : x < 0 <;> simp [scl, hx] <;> omega

theorem scl_zero (s : Bool) (e L : Int) : scl s 0 e L = 0 := by cases s <;> simp [scl]

/-- The exact sum `next_plus` forms, at the lower exponent `L = min(e, Etiny - 1)`. -/
theorem exactSum_next (c : Ctx) (s : Bool) (co : Nat) (e : Int) :
    exactSum s co e false 1 (c.etiny - 1) = scl s co e (min e (c.etiny - 1)) + gapd c (min e (c.etiny - 1)) := by
  cases s <;> simp [exactSum, scl, gapd]

theorem grid_ne_zero {c : Ctx} {L : Int} (hL : L < c.etiny) (u : Int) : u * gapD c L + gapd c L ≠ 0 := by
  have hD := gapD_eq hL
  have hd := gapd_pos c L
  intro h
  by_cases hu : 0 ≤ u
  · have : 0 ≤ u * gapD c L := Int.mul_nonneg hu (by omega)
    omega
  · have h2 : u * gapD c L ≤ (-1) * gapD c L := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    omega

/-- `next_plus` of every finite operand, when it returns, is the least representable value above
the operand (`+Infinity` when there is none), and leaves the flags unchanged. -/
theorem nextPlus_correct_fin (c : Ctx) (fl : List Signal) (hp : 1 ≤ c.prec) (hE : c.emin ≤ c.emax)
    (s : Bool) (co : Nat) (e : Int) (y : Dec) (fl' : List Signal)
    (h : (nextPlus c (.fin s co e)).run fl = .ok (y, fl')) :
    fl' = fl ∧ NextGoal c (min e (c.etiny - 1)) (scl s co e (min e (c.etiny - 1))) y := by
  have hLT : min e (c.etiny - 1) < c.etiny := by omega
  rw [nextPlus_fin_run] at h
  generalize hqd : quietCtx c .ceiling = q at h
  have hqp : 1 ≤ q.prec := by rw [← hqd]; exact hp
  have hqE : q.emin ≤ q.emax := by rw [← hqd]; exact hE
  have hqr : q.rounding = .ceiling := by rw [← hqd]; rfl
  have hqt : q.traps = [] := by rw [← hqd]; rfl
  have hqT : q.etiny = c.etiny := by rw [← hqd]; rfl
  have hfin : ∀ y X, CeilGoal q (min e (c.etiny - 1)) X y → CeilGoal c (min e (c.etiny - 1)) X y := by
    intro y X hg; subst hqd; exact hg
  by_cases hc : co = 0
  · subst hc
    have hz := (fixExact_proven q fl hqp).2.1 s e
    obtain ⟨ne, fl2, hfz⟩ : ∃ ne fl2, (fix q (.fin s 0 e)).run fl = .ok (.fin s 0 ne, fl2) := by
      rw [hz]
      split <;> split
      all_goals first
        | exact ⟨e, fl, rfl⟩
        | exact ⟨_, _, (sigRun_noTraps q hqt _ fl _).choose_spec⟩
    have hcm : cmpVal (.fin s 0 ne) (.fin s 0 e) = .eq := by simp [cmpVal]
    rw [hfz] at h
    simp only [hcm, ne_eq, not_true_eq_false, ↓reduceIte] at h
    rw [add_zero_left q fl2 hqp s e false 1 (q.etiny - 1) (by decide), hqT] at h
    generalize hE2 : max (min e (c.etiny - 1)) (c.etiny - 1 - ↑q.prec - 1) = E2 at h
    cases hfs : fixSpec q false (1 * 10 ^ (c.etiny - 1 - E2).toNat) E2 fl2 with
    | error x => rw [hfs] at h; exact absurd h (by simp)
    | ok p =>
      obtain ⟨y', fl3⟩ := p
      rw [hfs] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨rfl, ?_⟩
      have hg := ceil_fixSpec q hqp hqE hqr hqt false _ E2 (min e (c.etiny - 1))
        (Nat.mul_ne_zero (by decide) (Nat.pos_iff_ne_zero.mp (pow10_pos _)))
        (by omega) (by omega) fl2 fl3 y' hfs
      have hv : scl false (1 * 10 ^ (c.etiny - 1 - E2).toNat) E2 (min e (c.etiny - 1)) =
          scl s 0 e (min e (c.etiny - 1)) + gapd c (min e (c.etiny - 1)) := by
        rw [scl_zero]
        have : (c.etiny - 1 - E2).toNat + (E2 - min e (c.etiny - 1)).toNat =
            (c.etiny - 1 - min e (c.etiny - 1)).toNat := by omega
        simp only [scl, gapd, Bool.false_eq_true, ↓reduceIte, Nat.one_mul, ← Nat.pow_add, this]
        omega
      rw [hv] at hg
      exact next_of_ceil_add hLT ⟨0, by rw [scl_zero, Int.zero_mul]⟩ (hfin _ _ hg)
  · have hfx := fixExact_fin q s co e fl hqp hc
    rw [hfx] at h
    cases hfs : fixSpec q s co e fl with
    | error x => rw [hfs] at h; exact absurd h (by simp)
    | ok p =>
      obtain ⟨v, fl2⟩ := p
      rw [hfs] at h
      simp only at h
      have hg := hfin _ _ (ceil_fixSpec q hqp hqE hqr hqt s co e (min e (c.etiny - 1)) hc (by omega)
        (by omega) fl fl2 v hfs)
      by_cases hcmp : cmpVal v (.fin s co e) ≠ .eq
      · simp only [hcmp, ne_eq, not_false_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rfl, next_of_ceil_ne hg ?_⟩
        intro sv cv ev hv hT heq
        subst hv
        rw [cmpVal_fin_exact, ne_eq, finOrder_eq_iff sv cv ev s co e (min e (c.etiny - 1)) (by omega)
          (by omega)] at hcmp
        exact hcmp heq
      · simp only [hcmp, ne_eq, not_false_eq_true, ↓reduceIte, Decidable.not_not] at h
        simp only [ne_eq, Decidable.not_not] at hcmp
        -- the rounding kept the value: it is finite, on the grid of 10^Etiny
        obtain ⟨u, hu⟩ : ∃ u, scl s co e (min e (c.etiny - 1)) = u * gapD c (min e (c.etiny - 1)) := by
          rcases hg with ⟨rfl, _⟩ | ⟨sv, cv, ev, rfl, h1, _, _, _⟩
          · simp [cmpVal] at hcmp
          · rw [cmpVal_fin_exact, finOrder_eq_iff sv cv ev s co e (min e (c.etiny - 1)) (by omega)
              (by omega)] at hcmp
            obtain ⟨w, hw⟩ := fin_grid c (min e (c.etiny - 1)) sv cv ev h1 (by omega)
            exact ⟨w, by rw [← hcmp, hw]⟩
        cases hadd : (add q (.fin s co e) (.fin false 1 (q.etiny - 1))).run fl2 with
        | error x => rw [hadd] at h; exact absurd h (by simp)
        | ok p =>
        obtain ⟨y', fl3⟩ := p
        rw [hadd] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rfl, ?_⟩
        rw [add_fin_exact q fl2 hqp s co e false 1 (q.etiny - 1) hc (by decide), hqT] at hadd
        have hsum := exactSum_next c s co e
        split at hadd
        · exact absurd hadd (by simp)
        split at hadd
        · exact absurd hadd (by simp)
        split at hadd
        · rename_i h0
          rw [hsum, hu] at h0
          exact absurd h0 (grid_ne_zero hLT u)
        rename_i h0
        split at hadd
        · exact absurd hadd (by simp)
        have hg2 := hfin _ _ (ceil_fixSpec q hqp hqE hqr hqt _ _ _ (min e (c.etiny - 1))
          (by intro hz; exact h0 (Int.natAbs_eq_zero.mp hz)) (Int.le_refl _) (by omega) fl2 fl3 _ hadd)
        rw [scl_natAbs, hsum] at hg2
        exact next_of_ceil_add hLT ⟨u, hu⟩ hg2

/-! ## `next_plus` returns below the int/str limit -/

/-- `_fix` in a context that traps nothing and whose `prec + 1` is within the int/str limit
always returns. -/
theorem fixSpec_ok (q : Ctx) (hp : 1 ≤ q.prec) (htr : q.traps = []) (hlim : q.prec + 1 ≤ maxStrDigits)
    (neg : Bool) (co : Nat) (e : Int) (hc : co ≠ 0) (fl : List Signal) :
    ∃ r, fixSpec q neg co e fl = .ok r := by
  unfold fixSpec
  simp only
  split
  · exact ⟨_, (sigRun_noTraps q htr _ fl _).choose_spec⟩
  · split
    · split
      · exact ⟨_, (sigRun_noTraps q htr _ fl _).choose_spec⟩
      · exact ⟨_, (sigRun_noTraps q htr _ fl _).choose_spec⟩
    · rename_i _ hk
      split
      · rename_i hbad
        exfalso
        have hnd := numDigits_bounds hc
        generalize hk' : (max ((numDigits co : Int) + e - q.prec) (q.emin - q.prec + 1) - e).toNat = k at hbad
        have hq0 : co / 10 ^ k < 10 ^ q.prec := by
          rw [Nat.div_lt_iff_lt_mul (pow10_pos k), ← Nat.pow_add]
          exact Nat.lt_of_lt_of_le hnd.2 (pow10_le (by omega))
        have h1 := roundSpec_le q.rounding neg (co / 10 ^ k) (co % 10 ^ k) (10 ^ k)
        have h2 : roundSpec q.rounding neg (co / 10 ^ k) (co % 10 ^ k) (10 ^ k) < 10 ^ (q.prec + 1) := by
          have : 10 ^ q.prec < 10 ^ (q.prec + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
          omega
        have := (numDigits_le_iff (by omega)).mpr h2
        omega
      · exact ⟨_, (sigRun_noTraps q htr _ fl _).choose_spec⟩

theorem natAbs_sum_le (s : Bool) (a b : Nat) :
    ((if s then -1 else 1) * (a : Int) + 1 * (b : Int)).natAbs ≤ a + b := by
  cases s <;> simp <;> omega

theorem numDigits_le_of_lt {n j : Nat} (hj : 0 < j) (h : n < 10 ^ j) : numDigits n ≤ j :=
  (numDigits_le_iff hj).mpr h

/-- The digits `__add__` formats for `x + 1E(eb)` (`str(result.int)` after `_normalize`) are at
most the operand's digits plus `prec + 3`. -/
theorem workDigits_le (p : Nat) (hp : 1 ≤ p) (s : Bool) (co : Nat) (hc : co ≠ 0) (e eb : Int) :
    (numDigits (exactSum s co e false 1 eb).natAbs : Int) + min e eb - addWorkExp p co e 1 eb ≤
      numDigits co + p + 3 := by
  have hnd := numDigits_bounds hc
  have hS := natAbs_sum_le s (co * 10 ^ (e - min e eb).toNat) (1 * 10 ^ (eb - min e eb).toNat)
  have hsum : exactSum s co e false 1 eb =
      (if s then -1 else 1) * ((co * 10 ^ (e - min e eb).toNat : Nat) : Int) +
        1 * ((1 * 10 ^ (eb - min e eb).toNat : Nat) : Int) := by
    simp [exactSum]
  rw [hsum]
  generalize hN : ((if s then -1 else 1) * ((co * 10 ^ (e - min e eb).toNat : Nat) : Int) +
        1 * ((1 * 10 ^ (eb - min e eb).toNat : Nat) : Int)).natAbs = N at hS
  have h1 : numDigits (1 : Nat) = 1 := rfl
  simp only [addWorkExp, normExp, normSub, normX, h1]
  by_cases hlt : e < eb
  · -- the operand 1E(eb) has the larger exponent
    simp only [hlt, ↓reduceIte]
    obtain ⟨d, hd⟩ : ∃ d : Nat, (d : Int) = eb - e := ⟨(eb - e).toNat, by omega⟩
    have e1 : (e - min e eb).toNat = 0 := by omega
    have e2 : (eb - min e eb).toNat = d := by omega
    rw [e1, e2] at hS
    simp only [Nat.pow_zero, Nat.mul_one, Nat.one_mul] at hS
    split
    · rename_i hsub
      have hco : co < 10 ^ (d - 1) := Nat.lt_of_lt_of_le hnd.2 (pow10_le (by omega))
      have hd1 : 10 ^ d = 10 * 10 ^ (d - 1) := by
        rw [← Nat.pow_succ']; congr 1; omega
      have : N < 10 ^ (d + 1) := by rw [Nat.pow_succ, hd1]; omega
      have := numDigits_le_of_lt (by omega) this
      omega
    · rename_i hsub
      have hmx : co + 10 ^ d < 10 ^ (max (numDigits co) d + 1) := by
        have a1 : co < 10 ^ max (numDigits co) d := Nat.lt_of_lt_of_le hnd.2 (pow10_le (by omega))
        have a2 : 10 ^ d ≤ 10 ^ max (numDigits co) d := pow10_le (by omega)
        rw [Nat.pow_succ]; omega
      have := numDigits_le_of_lt (by omega) (Nat.lt_of_le_of_lt hS hmx)
      omega
  · simp only [hlt, ↓reduceIte]
    obtain ⟨d, hd⟩ : ∃ d : Nat, (d : Int) = e - eb := ⟨(e - eb).toNat, by omega⟩
    have e1 : (e - min e eb).toNat = d := by omega
    have e2 : (eb - min e eb).toNat = 0 := by omega
    rw [e1, e2] at hS
    simp only [Nat.pow_zero, Nat.mul_one] at hS
    have hb : co * 10 ^ d + 1 < 10 ^ (numDigits co + d + 1) := by
      have a1 : co * 10 ^ d < 10 ^ numDigits co * 10 ^ d := Nat.mul_lt_mul_of_pos_right hnd.2 (pow10_pos d)
      rw [← Nat.pow_add] at a1
      have a2 : 10 ^ (numDigits co + d) < 10 ^ (numDigits co + d + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
      omega
    have := numDigits_le_of_lt (by omega) (Nat.lt_of_le_of_lt hS hb)
    split
    · omega
    · omega

/-- `next_plus` of a finite operand returns, flags untouched, whenever its coefficient has at most
`4300 - prec - 3` digits (beyond that `__add__`'s `str(result.int)` can hit the int/str limit). -/
theorem nextPlus_ok_fin (c : Ctx) (fl : List Signal) (hp : 1 ≤ c.prec) (s : Bool) (co : Nat) (e : Int)
    (hd : numDigits co + c.prec + 3 ≤ maxStrDigits) :
    ∃ y, (nextPlus c (.fin s co e)).run fl = .ok (y, fl) := by
  rw [nextPlus_fin_run]
  generalize hqd : quietCtx c .ceiling = q
  have hqp : 1 ≤ q.prec := by rw [← hqd]; exact hp
  have hqt : q.traps = [] := by rw [← hqd]; rfl
  have hqP : q.prec = c.prec := by rw [← hqd]; rfl
  have hlim : q.prec + 1 ≤ maxStrDigits := by have := numDigits_pos co; omega
  have hzero : ∀ sz ez fl0, ∃ r, (fix q (.fin sz 0 ez)).run fl0 = .ok r := by
    intro sz ez fl0
    rw [(fixExact_proven q fl0 hqp).2.1 sz ez]
    split <;> split
    all_goals first
      | exact ⟨_, rfl⟩
      | exact ⟨_, (sigRun_noTraps q hqt _ fl0 _).choose_spec⟩
  have haddOk : ∀ fl2, ∃ r, (add q (.fin s co e) (.fin false 1 (q.etiny - 1))).run fl2 = .ok r := by
    intro fl2
    by_cases hc : co = 0
    · subst hc
      rw [add_zero_left q fl2 hqp s e false 1 (q.etiny - 1) (by decide)]
      exact fixSpec_ok q hqp hqt hlim _ _ _ (Nat.mul_ne_zero (by decide)
        (Nat.pos_iff_ne_zero.mp (pow10_pos _))) fl2
    · rw [add_fin_exact q fl2 hqp s co e false 1 (q.etiny - 1) hc (by decide)]
      have hw := workDigits_le q.prec hqp s co hc e (q.etiny - 1)
      have h1 : ¬ maxStrDigits < numDigits co := by omega
      have h2 : ¬ maxStrDigits < numDigits 1 := by decide
      simp only [h1, h2, ↓reduceIte]
      split
      · exact hzero _ _ fl2
      · split
        · rename_i hbad; exfalso; omega
        · rename_i hz _
          exact fixSpec_ok q hqp hqt hlim _ _ _ (fun h0 => hz (Int.natAbs_eq_zero.mp h0)) fl2
  by_cases hc : co = 0
  · subst hc
    obtain ⟨⟨v, fl2⟩, hf⟩ := hzero s e fl
    rw [hf]
    simp only
    split
    · exact ⟨_, rfl⟩
    · obtain ⟨⟨y, fl3⟩, ha⟩ := haddOk fl2
      rw [ha]
      exact ⟨y, rfl⟩
  · obtain ⟨⟨v, fl2⟩, hf⟩ := fixSpec_ok q hqp hqt hlim s co e hc fl
    rw [fixExact_fin q s co e fl hqp hc, hf]
    simp only
    split
    · exact ⟨_, rfl⟩
    · obtain ⟨⟨y, fl3⟩, ha⟩ := haddOk fl2
      rw [ha]
      exact ⟨y, rfl⟩

/-! ## `next_minus` is `next_plus` mirrored -/

/-- Negate the value of a result, keeping the flags. -/
def negRes (r : Py (Dec × List Signal)) : Py (Dec × List Signal) :=
  match r with
  | .ok (v, fl) => .ok (negate v, fl)
  | .error x => .error x

theorem sigRun_negate (c : Ctx) : ∀ (ss fl : List Signal) (v : Dec),
    sigRun c ss fl (negate v) = negRes (sigRun c ss fl v)
  | [], fl, v => rfl
  | s :: ss, fl, v => by
    simp only [sigRun]
    split
    · rfl
    · exact sigRun_negate c ss _ v

theorem negate_negate (d : Dec) : negate (negate d) = d := by
  cases d <;> simp [negate, Dec.withSign, Dec.neg]

theorem negRes_negRes (r : Py (Dec × List Signal)) : negRes (negRes r) = r := by
  cases r with
  | error x => rfl
  | ok p => obtain ⟨v, fl⟩ := p; simp [negRes, negate_negate]

theorem ite_negate_fin (neg b : Bool) (x : Dec) (cf : Nat) (ef : Int) :
    (if b = true then negate x else Dec.fin neg cf ef) = negate (if b = true then x else Dec.fin (!neg) cf ef) := by
  cases b <;> cases neg <;> rfl

/-- `_fix` under `ROUND_FLOOR` of a value is `_fix` under `ROUND_CEILING` of its negation, negated
(the two modes are each other's mirror, overflow values included). -/
theorem fixSpec_floor (c : Ctx) (neg : Bool) (co : Nat) (e : Int) (fl : List Signal) :
    fixSpec (quietCtx c .floor) neg co e fl = negRes (fixSpec (quietCtx c .ceiling) (!neg) co e fl) := by
  have hov : ∀ n, overflowResult (quietCtx c .floor) n = negate (overflowResult (quietCtx c .ceiling) (!n)) := by
    intro n; cases n <;> simp [overflowResult, quietCtx, negate, Dec.withSign, Dec.neg]
  have hrs : ∀ q0 r b, roundSpec (quietCtx c .floor).rounding neg q0 r b =
      roundSpec (quietCtx c .ceiling).rounding (!neg) q0 r b := by
    intro q0 r b; cases neg <;> simp [roundSpec, quietCtx]
  have hz : ∀ v : Dec, isZero (negate v) = isZero v := by
    intro v
    cases v with
    | fin n co e => cases co <;> rfl
    | _ => rfl
  unfold fixSpec
  simp only [hrs]
  have hp : (quietCtx c .floor).prec = (quietCtx c .ceiling).prec := rfl
  have he1 : (quietCtx c .floor).emax = (quietCtx c .ceiling).emax := rfl
  have he2 : (quietCtx c .floor).emin = (quietCtx c .ceiling).emin := rfl
  have hcl : (quietCtx c .floor).clamp = (quietCtx c .ceiling).clamp := rfl
  have htr : (quietCtx c .floor).traps = (quietCtx c .ceiling).traps := rfl
  have hsr : ∀ ss fl v, sigRun (quietCtx c .floor) ss fl v = sigRun (quietCtx c .ceiling) ss fl v := by
    intro ss; induction ss with
    | nil => intro fl v; rfl
    | cons s ss ih => intro fl v; simp only [sigRun, htr, ih]
  simp only [hp, he1, he2, hcl, hsr, hov]
  split
  · rw [sigRun_negate]
  · split
    · split
      · have : Dec.fin neg = fun c e => negate (Dec.fin (!neg) c e) := by
          funext c e; cases neg <;> rfl
        rw [this, sigRun_negate]
      · have : Dec.fin neg co e = negate (Dec.fin (!neg) co e) := by cases neg <;> rfl
        rw [this, sigRun_negate]
    · split
      · rfl
      · simp only [ite_negate_fin neg]
        rw [hz, sigRun_negate]

theorem quiet_prec (c : Ctx) (m : Rounding) : (quietCtx c m).prec = c.prec := rfl
theorem quiet_etiny (c : Ctx) (m : Rounding) : (quietCtx c m).etiny = c.etiny := rfl
theorem quiet_emin (c : Ctx) (m : Rounding) : (quietCtx c m).emin = c.emin := rfl
theorem quiet_emax (c : Ctx) (m : Rounding) : (quietCtx c m).emax = c.emax := rfl
theorem quiet_clamp (c : Ctx) (m : Rounding) : (quietCtx c m).clamp = c.clamp := rfl

theorem sigRun_congr (c1 c2 : Ctx) (h : c1.traps = c2.traps) :
    ∀ (ss fl : List Signal) (v : Dec), sigRun c1 ss fl v = sigRun c2 ss fl v
  | [], _, _ => rfl
  | s :: ss, fl, v => by
    simp only [sigRun, h]
    split
    · rfl
    · exact sigRun_congr c1 c2 h ss _ v

theorem zero_branch_neg (q1 q2 : Ctx) (hs : ∀ ss fl v, sigRun q1 ss fl v = sigRun q2 ss fl v)
    (P : Prop) [Decidable P] (neg : Bool) (x e : Int) (fl : List Signal) :
    (if P then sigRun q1 [.clamped] fl (.fin neg 0 x) else .ok (.fin neg 0 e, fl)) =
      negRes (if P then sigRun q2 [.clamped] fl (.fin (!neg) 0 x) else .ok (.fin (!neg) 0 e, fl)) := by
  have hv : ∀ x, Dec.fin neg 0 x = negate (Dec.fin (!neg) 0 x) := by intro x; cases neg <;> rfl
  by_cases hP : P
  · rw [if_pos hP, if_pos hP, hv, hs, sigRun_negate]
  · rw [if_neg hP, if_neg hP, hv]; rfl

theorem fix_floor (c : Ctx) (hp : 1 ≤ c.prec) (neg : Bool) (co : Nat) (e : Int) (fl : List Signal) :
    (fix (quietCtx c .floor) (.fin neg co e)).run fl =
      negRes ((fix (quietCtx c .ceiling) (.fin (!neg) co e)).run fl) := by
  by_cases hc : co = 0
  · subst hc
    rw [(fixExact_proven (quietCtx c .floor) fl hp).2.1 neg e,
      (fixExact_proven (quietCtx c .ceiling) fl hp).2.1 (!neg) e]
    have hv : ∀ x, Dec.fin neg 0 x = negate (Dec.fin (!neg) 0 x) := by intro x; cases neg <;> rfl
    have hs := sigRun_congr (quietCtx c .floor) (quietCtx c .ceiling) rfl
    simp only [quiet_emin, quiet_emax, quiet_clamp, quiet_prec]
    exact zero_branch_neg _ _ hs _ neg _ e fl
  · rw [fixExact_fin (quietCtx c .floor) neg co e fl hp hc, fixExact_fin (quietCtx c .ceiling) (!neg) co e fl hp hc,
      fixSpec_floor]

theorem exactSum_neg (s : Bool) (co : Nat) (e eb : Int) :
    exactSum s co e true 1 eb = -(exactSum (!s) co e false 1 eb) := by
  cases s <;> simp [exactSum] <;> omega

/-- `__add__` under `ROUND_FLOOR` of `x + (-1E(eb))` is `__add__` under `ROUND_CEILING` of
`(-x) + 1E(eb)`, negated. -/
theorem add_floor (c : Ctx) (hp : 1 ≤ c.prec) (s : Bool) (co : Nat) (e eb : Int) (fl : List Signal) :
    (add (quietCtx c .floor) (.fin s co e) (.fin true 1 eb)).run fl =
      negRes ((add (quietCtx c .ceiling) (.fin (!s) co e) (.fin false 1 eb)).run fl) := by
  by_cases hc : co = 0
  · subst hc
    rw [add_zero_left (quietCtx c .floor) fl hp s e true 1 eb (by decide),
      add_zero_left (quietCtx c .ceiling) fl hp (!s) e false 1 eb (by decide),
      quiet_prec, quiet_prec, fixSpec_floor]
    rfl
  · rw [add_fin_exact (quietCtx c .floor) fl hp s co e true 1 eb hc (by decide),
      add_fin_exact (quietCtx c .ceiling) fl hp (!s) co e false 1 eb hc (by decide), exactSum_neg, quiet_prec,
      quiet_prec]
    split
    · rfl
    split
    · rfl
    split
    · rename_i h0
      have h0' : exactSum (!s) co e false 1 eb = 0 := by omega
      simp only [h0', ↓reduceIte]
      have h1 : decide ((quietCtx c .floor).rounding = .floor) = true := rfl
      have h2 : decide ((quietCtx c .ceiling).rounding = .floor) = false := rfl
      rw [h1, h2, fix_floor c hp]
      rfl
    · rename_i h0
      have h0' : ¬ exactSum (!s) co e false 1 eb = 0 := by omega
      simp only [h0', ↓reduceIte, Int.natAbs_neg]
      split
      · rfl
      · have hd : decide (-exactSum (!s) co e false 1 eb < 0) = !decide (exactSum (!s) co e false 1 eb < 0) := by
          by_cases hx : exactSum (!s) co e false 1 eb < 0 <;> simp [hx] <;> omega
        rw [hd, fixSpec_floor, Bool.not_not]

theorem sgnVal_not (n : Bool) (x : Nat) : sgnVal (!n) x = -sgnVal n x := by
  cases n <;> simp [sgnVal]

theorem cmp_negate (v : Dec) (s : Bool) (co : Nat) (e : Int) :
    (cmpVal (negate v) (.fin s co e) = .eq) ↔ (cmpVal v (.fin (!s) co e) = .eq) := by
  cases v with
  | fin n c1 e1 =>
    show cmpVal (.fin (!n) c1 e1) (.fin s co e) = .eq ↔ cmpVal (.fin n c1 e1) (.fin (!s) co e) = .eq
    rw [cmpVal_fin_exact, cmpVal_fin_exact]
    simp only [finOrder, ordOf_eq_iff, sgnVal_not]
    omega
  | inf n =>
    show (cmpVal (.inf (!n)) (.fin s co e) = .eq) ↔ (cmpVal (.inf n) (.fin (!s) co e) = .eq)
    cases n <;> simp [cmpVal]
  | nan n sg p =>
    show (cmpVal (.nan (!n) sg p) (.fin s co e) = .eq) ↔ (cmpVal (.nan n sg p) (.fin (!s) co e) = .eq)
    constructor <;> intro _ <;> rfl

theorem nextMinus_fin_run (c : Ctx) (s : Bool) (co : Nat) (e : Int) (fl : List Signal) :
    (nextMinus c (.fin s co e)).run fl =
      match (fix (quietCtx c .floor) (.fin s co e)).run fl with
      | .error x => .error x
      | .ok (v, fl2) =>
        if cmpVal v (.fin s co e) ≠ .eq then .ok (v, fl)
        else match (sub (quietCtx c .floor) (.fin s co e)
            (.fin false 1 ((quietCtx c .floor).etiny - 1))).run fl2 with
          | .error x => .error x
          | .ok (y, _) => .ok (y, fl) := by
  simp only [nextMinus, checkNans, isinfinity, StateT.run, bind, StateT.bind, pure, StateT.pure,
    Except.bind, Except.pure]
  simp only [show ¬ ((0 : Int) = 1) by decide, show ¬ ((0 : Int) = -1) by decide, ↓reduceIte]
  unfold quietly
  simp only [StateT.bind, bind, Except.bind, pure, Except.pure]
  cases fix (quietCtx c .floor) (.fin s co e) fl with
  | error x => rfl
  | ok p =>
    obtain ⟨v, fl2⟩ := p
    simp only
    by_cases hc : cmpVal v (.fin s co e) ≠ .eq
    · simp only [hc, ↓reduceIte, ne_eq, not_false_eq_true]; rfl
    · simp only [hc, ↓reduceIte]
      cases sub (quietCtx c .floor) (.fin s co e) (.fin false 1 ((quietCtx c .floor).etiny - 1)) fl2 with
      | error x => rfl
      | ok p => rfl

/-- `next_minus` is `next_plus` mirrored: `x.next_minus() == x.copy_negate().next_plus().copy_negate()`
for every operand, NaNs and infinities included, with the same flags. -/
theorem nextMinus_twin_fin (c : Ctx) (hp : 1 ≤ c.prec) (s : Bool) (co : Nat) (e : Int) (fl : List Signal) :
    (nextMinus c (.fin s co e)).run fl = negRes ((nextPlus c (.fin (!s) co e)).run fl) := by
  rw [nextMinus_fin_run, nextPlus_fin_run, fix_floor c hp]
  cases hf : (fix (quietCtx c .ceiling) (.fin (!s) co e)).run fl with
  | error x => rfl
  | ok p =>
    obtain ⟨v, fl2⟩ := p
    simp only [negRes]
    have hcm := cmp_negate v s co e
    by_cases hc : cmpVal v (.fin (!s) co e) = .eq
    · have hc' : cmpVal (negate v) (.fin s co e) = .eq := hcm.mpr hc
      simp only [hc, hc', ne_eq, not_true_eq_false, ↓reduceIte]
      rw [show (quietCtx c .floor).etiny = (quietCtx c .ceiling).etiny from rfl]
      rw [sub_fin_run, show (!false) = true from rfl, add_floor c hp]
      cases (add (quietCtx c .ceiling) (.fin (!s) co e) (.fin false 1 ((quietCtx c .ceiling).etiny - 1))).run fl2 with
      | error x => rfl
      | ok p => rfl
    · have hc' : ¬ cmpVal (negate v) (.fin s co e) = .eq := fun h => hc (hcm.mp h)
      simp only [hc, hc', ne_eq, not_false_eq_true, ↓reduceIte]

/-! ## Infinities and NaNs -/

theorem nextPlus_inf (c : Ctx) (fl : List Signal) :
    (nextPlus c (.inf false)).run fl = .ok (.inf false, fl) ∧
    (nextPlus c (.inf true)).run fl = .ok (.fin true (10 ^ c.prec - 1) c.etop, fl) := by
  constructor <;> simp [nextPlus, checkNans, isinfinity] <;> rfl

theorem nextMinus_inf (c : Ctx) (fl : List Signal) :
    (nextMinus c (.inf true)).run fl = .ok (.inf true, fl) ∧
    (nextMinus c (.inf false)).run fl = .ok (.fin false (10 ^ c.prec - 1) c.etop, fl) := by
  constructor <;> simp [nextMinus, checkNans, isinfinity] <;> rfl

theorem nextPlus_nan (c : Ctx) (fl : List Signal) (neg : Bool) (p : Nat) :
    (nextPlus c (.nan neg false p)).run fl = .ok (.nan neg false (p % 10 ^ nanDigits c), fl) ∧
    (nextPlus c (.nan neg true p)).run fl = afterSig c .invalidOperation fl (.nan neg false (p % 10 ^ nanDigits c)) := by
  refine ⟨?_, ?_⟩
  · simp [nextPlus, checkNans, fixNan_spec]; rfl
  · rw [← sNaN_run]; simp [nextPlus, checkNans]

theorem nextMinus_nan (c : Ctx) (fl : List Signal) (neg : Bool) (p : Nat) :
    (nextMinus c (.nan neg false p)).run fl = .ok (.nan neg false (p % 10 ^ nanDigits c), fl) ∧
    (nextMinus c (.nan neg true p)).run fl = afterSig c .invalidOperation fl (.nan neg false (p % 10 ^ nanDigits c)) := by
  refine ⟨?_, ?_⟩
  · simp [nextMinus, checkNans, fixNan_spec]; rfl
  · rw [← sNaN_run]; simp [nextMinus, checkNans]

theorem negRes_afterSig (c : Ctx) (s : Signal) (fl : List Signal) (v : Dec) :
    negRes (afterSig c s fl v) = afterSig c s fl (negate v) := by
  unfold afterSig; split <;> rfl

/-- `x.next_minus()` is `x.copy_negate().next_plus().copy_negate()`, flags and exceptions included,
for every operand. -/
theorem nextMinus_twin (c : Ctx) (hp : 1 ≤ c.prec) (a : Dec) (fl : List Signal) :
    (nextMinus c a).run fl = negRes ((nextPlus c (copyNegate a)).run fl) := by
  cases a with
  | fin s co e => exact nextMinus_twin_fin c hp s co e fl
  | inf n =>
    cases n
    · show _ = negRes ((nextPlus c (.inf true)).run fl)
      rw [(nextMinus_inf c fl).2, (nextPlus_inf c fl).2]; rfl
    · show _ = negRes ((nextPlus c (.inf false)).run fl)
      rw [(nextMinus_inf c fl).1, (nextPlus_inf c fl).1]; rfl
  | nan n sg p =>
    show _ = negRes ((nextPlus c (.nan (!n) sg p)).run fl)
    cases sg
    · rw [(nextMinus_nan c fl n p).1, (nextPlus_nan c fl (!n) p).1]
      cases n <;> rfl
    · rw [(nextMinus_nan c fl n p).2, (nextPlus_nan c fl (!n) p).2, negRes_afterSig]
      cases n <;> rfl

/-! ## `next_minus` is the largest representable value below -/

/-- What `next_minus` gives for the value `X` (scaled to `L`): `-Infinity` when no representable
value is below `X`, otherwise the largest representable value below it. -/
def PrevGoal (c : Ctx) (L X : Int) (y : Dec) : Prop :=
  (y = .inf true ∧ ∀ Z, RepAt c L Z → X ≤ Z) ∨
  (∃ sy cy ey, y = .fin sy cy ey ∧ cy < 10 ^ c.prec ∧ c.etiny ≤ ey ∧ ey ≤ c.etop ∧
     scl sy cy ey L < X ∧ ∀ Z, RepAt c L Z → Z < X → Z ≤ scl sy cy ey L)

theorem scl_not (b : Bool) (cz : Nat) (ez L : Int) : scl (!b) cz ez L = -scl b cz ez L := by
  cases b <;> simp [scl]

theorem repAt_neg {c : Ctx} {L Z : Int} (h : RepAt c L Z) : RepAt c L (-Z) := by
  obtain ⟨b, cz, ez, h1, h2, h3, rfl⟩ := h
  exact ⟨!b, cz, ez, h1, h2, h3, (scl_not b cz ez L).symm⟩

theorem prev_of_next {c : Ctx} {L X : Int} {y : Dec} (h : NextGoal c L (-X) (negate y)) : PrevGoal c L X y := by
  rcases h with ⟨h1, h2⟩ | ⟨sy, cy, ey, h1, h2, h3, h4, h5, h6⟩
  · left
    refine ⟨?_, fun Z hZ => ?_⟩
    · cases y with
      | inf n => cases n <;> simp_all [negate, Dec.withSign, Dec.neg]
      | fin _ _ _ => simp [negate, Dec.withSign] at h1
      | nan _ _ _ => simp [negate, Dec.withSign] at h1
    · have := h2 (-Z) (repAt_neg hZ); omega
  · right
    have hy : y = .fin (!sy) cy ey := by
      cases y with
      | fin n c1 e1 =>
        simp only [negate, Dec.withSign, Dec.neg, Dec.fin.injEq] at h1
        obtain ⟨rfl, rfl, rfl⟩ := h1
        simp
      | inf _ => simp [negate, Dec.withSign] at h1
      | nan _ _ _ => simp [negate, Dec.withSign] at h1
    refine ⟨!sy, cy, ey, hy, h2, h3, h4, ?_, fun Z hZ hZX => ?_⟩
    · rw [scl_not]; omega
    · have := h6 (-Z) (repAt_neg hZ) (by omega)
      rw [scl_not]; omega

/-- `next_minus` of every finite operand, when it returns, is the largest representable value below
it (`-Infinity` when there is none), and leaves the flags unchanged. -/
theorem nextMinus_correct_fin (c : Ctx) (fl : List Signal) (hp : 1 ≤ c.prec) (hE : c.emin ≤ c.emax)
    (s : Bool) (co : Nat) (e : Int) (y : Dec) (fl' : List Signal)
    (h : (nextMinus c (.fin s co e)).run fl = .ok (y, fl')) :
    fl' = fl ∧ PrevGoal c (min e (c.etiny - 1)) (scl s co e (min e (c.etiny - 1))) y := by
  rw [nextMinus_twin_fin c hp] at h
  cases hn : (nextPlus c (.fin (!s) co e)).run fl with
  | error x => rw [hn] at h; exact absurd h (by simp [negRes])
  | ok p =>
    obtain ⟨y', fl2⟩ := p
    rw [hn] at h
    simp only [negRes, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨h1, h2⟩ := nextPlus_correct_fin c fl hp hE (!s) co e y' fl2 hn
    refine ⟨h1, prev_of_next ?_⟩
    rw [negate_negate, ← scl_not]
    exact h2

theorem nextMinus_ok_fin (c : Ctx) (fl : List Signal) (hp : 1 ≤ c.prec) (s : Bool) (co : Nat) (e : Int)
    (hd : numDigits co + c.prec + 3 ≤ maxStrDigits) :
    ∃ y, (nextMinus c (.fin s co e)).run fl = .ok (y, fl) := by
  obtain ⟨y, hy⟩ := nextPlus_ok_fin c fl hp (!s) co e hd
  exact ⟨negate y, by rw [nextMinus_twin_fin c hp, hy]; rfl⟩

/-! ## `next_toward` -/

/-- The signals `next_toward` raises for its result (_pydecimal.py:3647-3663): `Overflow`,
`Inexact`, `Rounded` for an infinity; `Underflow`, `Subnormal`, `Inexact`, `Rounded` (and `Clamped`
for a zero) for a result whose adjusted exponent is below `Emin`; none otherwise. -/
def towardSigs (c : Ctx) (y : Dec) : List Signal :=
  if isinfinity y ≠ 0 then [.overflow, .inexact, .rounded]
  else if y.adjusted < c.emin then
    [.underflow, .subnormal, .inexact, .rounded] ++ (if isZero y then [.clamped] else [])
  else []

theorem toward_tail (c : Ctx) (y : Dec) (fl : List Signal) :
    ((do
      if isinfinity y ≠ 0 then
        raiseSig c .overflow
        raiseSig c .inexact
        raiseSig c .rounded
      else if y.adjusted < c.emin then
        raiseSig c .underflow
        raiseSig c .subnormal
        raiseSig c .inexact
        raiseSig c .rounded
        if isZero y then raiseSig c .clamped
      return y) : DM Dec).run fl = sigRun c (towardSigs c y) fl y := by
  unfold towardSigs
  by_cases h1 : isinfinity y ≠ 0
  · rw [if_pos h1, if_pos h1]
    simp only [bind_assoc, raiseSig_bind, pure_run, sigRun_cons, sigRun]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : y.adjusted < c.emin
    · rw [if_pos h2, if_pos h2]
      by_cases h3 : isZero y = true
      · rw [if_pos h3, if_pos h3]
        simp only [bind_assoc, raiseSig_bind, pure_run, sigRun_cons, sigRun, List.cons_append,
          List.nil_append]
      · rw [if_neg h3, if_neg h3]
        simp only [bind_assoc, raiseSig_bind, pure_run, sigRun_cons, sigRun, List.append_nil, pure_bind]
    · rw [if_neg h2, if_neg h2]
      rfl

/-- `next_toward` (_pydecimal.py:3621-3665): NaN operands go through `_check_nans`; numerically
equal operands give `self.copy_sign(other)`; otherwise the result of `next_plus` (when
`self < other`) or `next_minus` (when `self > other`), with `towardSigs` raised on the caller's
context in order, the first trapped one raising. -/
def NextTowardExact : Prop :=
  ∀ (c : Ctx) (fl : List Signal),
    (∀ a b : Dec, nanKind a ≠ 0 ∨ nanKind b ≠ 0 → (nextToward c a b).run fl = nanSpec2 c a b fl) ∧
    (∀ a b : Dec, nanKind a = 0 → nanKind b = 0 →
      (nextToward c a b).run fl =
        if numOrder a b = .eq then .ok (copySign a b, fl)
        else match (if numOrder a b = .lt then nextPlus c a else nextMinus c a).run fl with
          | .error x => .error x
          | .ok (y, fl2) => sigRun c (towardSigs c y) fl2 y)

theorem nextTowardExact_proven : NextTowardExact := by
  intro c fl
  refine ⟨fun a b h => ?_, fun a b ha hb => ?_⟩
  · exact checkNans_return c a b fl _ (fun d => rfl) h
  · have hcmp := cmpVal_exact a b ha hb
    unfold nextToward
    rw [checkNans_none_bind c a b ha hb]
    simp only [cmpInt, hcmp]
    cases ho : numOrder a b with
    | eq => rfl
    | lt =>
      simp only [reduceCtorEq, ↓reduceIte, show ¬ ((-1 : Int) = 0) by decide]
      rw [bind_run]
      cases (nextPlus c a).run fl with
      | error x => rfl
      | ok p => obtain ⟨y, fl2⟩ := p; exact toward_tail c y fl2
    | gt =>
      simp only [reduceCtorEq, ↓reduceIte, show ¬ ((1 : Int) = 0) by decide,
        show ¬ ((1 : Int) = -1) by decide]
      rw [bind_run]
      cases (nextMinus c a).run fl with
      | error x => rfl
      | ok p => obtain ⟨y, fl2⟩ := p; exact toward_tail c y fl2

/-! ## `next_plus` of a finite operand, every outcome -/

/-- The result `r` of a computation in `next_plus`'s flag-ignoring copy, with the caller's flags
`fl` (the copy's flags are dropped, `_ignore_all_flags`). -/
def keepFl (fl : List Signal) : Py (Dec × List Signal) → Py (Dec × List Signal)
  | .error x => .error x
  | .ok (y, _) => .ok (y, fl)

/-- `next_plus` of a finite `±co·10^e` (_pydecimal.py:3612-3619) with `_fix` (`fixSpec`) and
`__add__` (`AddExact`'s cases) written out, in the copy `q` of the context that rounds toward `+∞`
and ignores every flag (`eb = Etiny - 1`):

* a zero: `_fix` keeps its value, and `0 + 1E(eb)` is `1E(eb)` padded to the exponent
  `max(min(e, eb), eb - prec - 1)` and rounded by `_fix`;
* otherwise `_fix(q)` of the operand (its own int/str-limit `ValueError` included); a value that
  differs from the operand is the result; else `__add__` of `1E(eb)`: `int(self._int)`'s
  `ValueError` for a coefficient of more than 4300 digits, the zero sum, `str(result.int)`'s
  `ValueError` when the working sum `_normalize` makes has more than 4300 digits, and otherwise the
  exact sum rounded by `_fix(q)`. -/
def nextPlusFinSpec (c : Ctx) (s : Bool) (co : Nat) (e : Int) (fl : List Signal) :
    Py (Dec × List Signal) :=
  let q := quietCtx c .ceiling
  let eb := c.etiny - 1
  if co = 0 then
    keepFl fl (fixSpec q false (1 * 10 ^ (eb - max (min e eb) (eb - c.prec - 1)).toNat)
      (max (min e eb) (eb - c.prec - 1)) fl)
  else match fixSpec q s co e fl with
    | .error x => .error x
    | .ok (v, _) =>
      if cmpVal v (.fin s co e) ≠ .eq then .ok (v, fl)
      else if maxStrDigits < numDigits co then .error (.valueError (limitToIntMsg (numDigits co)))
      else if exactSum s co e false 1 eb = 0 then keepFl fl ((fix q (.fin false 0 (min e eb))).run fl)
      else if (maxStrDigits : Int) < (numDigits (exactSum s co e false 1 eb).natAbs : Int) + min e eb -
          addWorkExp c.prec co e 1 eb then .error (.valueError limitToStrMsg)
      else keepFl fl (fixSpec q (decide (exactSum s co e false 1 eb < 0))
        (exactSum s co e false 1 eb).natAbs (min e eb) fl)

theorem match_keep (fl : List Signal) (r : Py (Dec × List Signal)) :
    (match r with
      | .error x => .error x
      | .ok (y, _) => .ok (y, fl)) = keepFl fl r := by
  cases r with
  | error x => rfl
  | ok p => rfl

theorem keep_sigRun (q : Ctx) (h : q.traps = []) (ss fl1 fl : List Signal) (v : Dec) :
    keepFl fl (sigRun q ss fl1 v) = .ok (v, fl) := by
  obtain ⟨fl', h'⟩ := sigRun_noTraps q h ss fl1 v
  rw [h']; rfl

/-- In a context that traps nothing, what `_fix` returns does not depend on the flags. -/
theorem fixSpec_keep (q : Ctx) (h : q.traps = []) (neg : Bool) (co : Nat) (e : Int)
    (fl1 fl2 fl : List Signal) :
    keepFl fl (fixSpec q neg co e fl1) = keepFl fl (fixSpec q neg co e fl2) := by
  unfold fixSpec
  simp only
  split
  · rw [keep_sigRun q h, keep_sigRun q h]
  · split
    · split
      · rw [keep_sigRun q h, keep_sigRun q h]
      · rw [keep_sigRun q h, keep_sigRun q h]
    · split
      · rfl
      · rw [keep_sigRun q h, keep_sigRun q h]

theorem fixZero_keep (q : Ctx) (hp : 1 ≤ q.prec) (h : q.traps = []) (neg : Bool) (e : Int)
    (fl1 fl2 fl : List Signal) :
    keepFl fl ((fix q (.fin neg 0 e)).run fl1) = keepFl fl ((fix q (.fin neg 0 e)).run fl2) := by
  rw [(fixExact_proven q fl1 hp).2.1 neg e, (fixExact_proven q fl2 hp).2.1 neg e]
  repeat' split
  all_goals first
    | rfl
    | rw [keep_sigRun q h, keep_sigRun q h]

theorem nextPlus_fin_spec (c : Ctx) (hp : 1 ≤ c.prec) (s : Bool) (co : Nat) (e : Int)
    (fl : List Signal) : (nextPlus c (.fin s co e)).run fl = nextPlusFinSpec c s co e fl := by
  rw [nextPlus_fin_run]
  have hqp : 1 ≤ (quietCtx c .ceiling).prec := hp
  have hqt : (quietCtx c .ceiling).traps = [] := rfl
  unfold nextPlusFinSpec
  simp only
  by_cases hc : co = 0
  · subst hc
    rw [if_pos rfl]
    obtain ⟨ne, fl2, hfz⟩ : ∃ ne fl2,
        (fix (quietCtx c .ceiling) (.fin s 0 e)).run fl = .ok (.fin s 0 ne, fl2) := by
      rw [(fixExact_proven _ fl hqp).2.1 s e]
      split <;> (try split) <;> first
        | exact ⟨e, fl, rfl⟩
        | exact ⟨_, _, (sigRun_noTraps _ hqt _ fl _).choose_spec⟩
    have hcm : cmpVal (.fin s 0 ne) (.fin s 0 e) = .eq := by simp [cmpVal]
    rw [hfz]
    simp only [hcm, ne_eq, not_true_eq_false, ↓reduceIte]
    rw [match_keep, add_zero_left _ fl2 hqp s e false 1 _ (by decide), quiet_etiny, quiet_prec]
    exact fixSpec_keep _ hqt _ _ _ fl2 fl fl
  · rw [if_neg hc, fixExact_fin _ s co e fl hqp hc]
    cases hfs : fixSpec (quietCtx c .ceiling) s co e fl with
    | error x => rfl
    | ok p =>
      obtain ⟨v, fl2⟩ := p
      simp only
      by_cases hcmp : cmpVal v (.fin s co e) ≠ .eq
      · rw [if_pos hcmp, if_pos hcmp]
      · rw [if_neg hcmp, if_neg hcmp, match_keep,
          add_fin_exact _ fl2 hqp s co e false 1 _ hc (by decide), quiet_etiny, quiet_prec]
        have h1 : ¬ maxStrDigits < numDigits 1 := by decide
        by_cases l1 : maxStrDigits < numDigits co
        · rw [if_pos l1, if_pos l1]; rfl
        · rw [if_neg l1, if_neg l1, if_neg h1]
          by_cases l2 : exactSum s co e false 1 (c.etiny - 1) = 0
          · rw [if_pos l2, if_pos l2]
            have hr : decide ((quietCtx c .ceiling).rounding = .floor) = false := rfl
            rw [hr]
            exact fixZero_keep _ hqp hqt _ _ fl2 fl fl
          · rw [if_neg l2, if_neg l2]
            by_cases l3 : (maxStrDigits : Int) < (numDigits (exactSum s co e false 1 (c.etiny - 1)).natAbs : Int) +
                min e (c.etiny - 1) - addWorkExp c.prec co e 1 (c.etiny - 1)
            · rw [if_pos l3, if_pos l3]; rfl
            · rw [if_neg l3, if_neg l3]
              exact fixSpec_keep _ hqt _ _ _ fl2 fl fl

/-! ## The statements -/

/-- `Decimal.next_plus` (_pydecimal.py:3598-3619; docstring "Returns the smallest representable
number larger than itself"), for every context (`prec ≥ 1`, `Emin ≤ Emax`) and flag state:

* a finite `±co·10^e`, when `next_plus` returns, gives the least representable value above it
  (`NextGoal`: finite with at most `prec` digits and an exponent in `[Etiny, Etop]`, above the
  operand, and at most every representable value above the operand; `+Infinity` when every
  representable value is at most the operand), and leaves the caller's flags as they were (it
  works in a copy that ignores every flag, so no trap fires);
* it does return for every finite operand whose coefficient has at most `4300 - prec - 3` digits;
* every outcome of a finite operand, the exceptions included, is `nextPlusFinSpec`: `_fix` toward
  `+∞` in the flag-ignoring copy (`fixSpec`, with its int/str-limit `ValueError` on an incremented
  coefficient of more than 4300 digits), and when that keeps the value, `__add__` of `1E(Etiny-1)`
  with its two int/str-limit `ValueError`s (`int(self._int)` for a coefficient of more than 4300
  digits, `str(result.int)` for a working sum of more than 4300 digits) and its `_fix`: so
  `Decimal((0, (1,) + (0,)*4299, -4299)).next_plus()` and `Decimal(1).next_plus(Context(prec=5000))`
  raise that `ValueError`, as they do on 3.15.2, and nothing else raises;
* `+Infinity` stays; `-Infinity` gives the most negative finite value `-(10^prec-1)·10^Etop`;
* a quiet NaN gives itself with its payload cut to `prec - clamp` digits; a signaling NaN
  signals InvalidOperation and gives that quiet NaN. -/
def NextPlusExact : Prop :=
  ∀ (c : Ctx) (fl : List Signal), 1 ≤ c.prec → c.emin ≤ c.emax →
    (∀ (s : Bool) (co : Nat) (e : Int) (y : Dec) (fl' : List Signal),
      (nextPlus c (.fin s co e)).run fl = .ok (y, fl') →
      fl' = fl ∧ NextGoal c (min e (c.etiny - 1)) (scl s co e (min e (c.etiny - 1))) y) ∧
    (∀ (s : Bool) (co : Nat) (e : Int), numDigits co + c.prec + 3 ≤ maxStrDigits →
      ∃ y, (nextPlus c (.fin s co e)).run fl = .ok (y, fl)) ∧
    (∀ (s : Bool) (co : Nat) (e : Int), (nextPlus c (.fin s co e)).run fl = nextPlusFinSpec c s co e fl) ∧
    (nextPlus c (.inf false)).run fl = .ok (.inf false, fl) ∧
    (nextPlus c (.inf true)).run fl = .ok (.fin true (10 ^ c.prec - 1) c.etop, fl) ∧
    (∀ (neg : Bool) (p : Nat),
      (nextPlus c (.nan neg false p)).run fl = .ok (.nan neg false (p % 10 ^ nanDigits c), fl) ∧
      (nextPlus c (.nan neg true p)).run fl =
        afterSig c .invalidOperation fl (.nan neg false (p % 10 ^ nanDigits c)))

theorem nextPlusExact_proven : NextPlusExact := by
  intro c fl hp hE
  exact ⟨fun s co e y fl' h => nextPlus_correct_fin c fl hp hE s co e y fl' h,
    fun s co e hd => nextPlus_ok_fin c fl hp s co e hd, fun s co e => nextPlus_fin_spec c hp s co e fl,
    (nextPlus_inf c fl).1, (nextPlus_inf c fl).2,
    fun neg p => nextPlus_nan c fl neg p⟩

/-- `Decimal.next_minus` (_pydecimal.py:3575-3596; docstring "Returns the largest representable
number smaller than itself"), for every context (`prec ≥ 1`, `Emin ≤ Emax`) and flag state:

* it is `next_plus` mirrored: `x.next_minus()` is `x.copy_negate().next_plus().copy_negate()`
  for every operand, the flags and any exception included (`ROUND_FLOOR` is `ROUND_CEILING`
  mirrored, and `x - 1E(Etiny-1)` is `-((-x) + 1E(Etiny-1))`);
* so a finite operand, when `next_minus` returns, gives the largest representable value below it
  (`PrevGoal`; `-Infinity` when every representable value is at least the operand), with the flags
  unchanged, and it returns for every coefficient of at most `4300 - prec - 3` digits;
* `-Infinity` stays, `+Infinity` gives the largest finite value; NaNs as in `next_plus`. -/
def NextMinusExact : Prop :=
  ∀ (c : Ctx) (fl : List Signal), 1 ≤ c.prec → c.emin ≤ c.emax →
    (∀ a : Dec, (nextMinus c a).run fl = negRes ((nextPlus c (copyNegate a)).run fl)) ∧
    (∀ (s : Bool) (co : Nat) (e : Int) (y : Dec) (fl' : List Signal),
      (nextMinus c (.fin s co e)).run fl = .ok (y, fl') →
      fl' = fl ∧ PrevGoal c (min e (c.etiny - 1)) (scl s co e (min e (c.etiny - 1))) y) ∧
    (∀ (s : Bool) (co : Nat) (e : Int), numDigits co + c.prec + 3 ≤ maxStrDigits →
      ∃ y, (nextMinus c (.fin s co e)).run fl = .ok (y, fl)) ∧
    (nextMinus c (.inf true)).run fl = .ok (.inf true, fl) ∧
    (nextMinus c (.inf false)).run fl = .ok (.fin false (10 ^ c.prec - 1) c.etop, fl) ∧
    (∀ (neg : Bool) (p : Nat),
      (nextMinus c (.nan neg false p)).run fl = .ok (.nan neg false (p % 10 ^ nanDigits c), fl) ∧
      (nextMinus c (.nan neg true p)).run fl =
        afterSig c .invalidOperation fl (.nan neg false (p % 10 ^ nanDigits c)))

theorem nextMinusExact_proven : NextMinusExact := by
  intro c fl hp hE
  exact ⟨fun a => nextMinus_twin c hp a fl, fun s co e y fl' h => nextMinus_correct_fin c fl hp hE s co e y fl' h,
    fun s co e hd => nextMinus_ok_fin c fl hp s co e hd, (nextMinus_inf c fl).1, (nextMinus_inf c fl).2,
    fun neg p => nextMinus_nan c fl neg p⟩

end PyLean.Decimal
